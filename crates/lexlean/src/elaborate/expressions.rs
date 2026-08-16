//! Conservative expression elaboration (SPEC.md §17.6): signature-driven
//! candidate filtering with metavariables for omitted implicit binders and
//! numeral expected types. Where conservative unification cannot choose
//! uniquely, elaboration rejects (I5).

use std::collections::BTreeMap;

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::elaborate::resolve::{LocalAlloc, ScopeStack};
use crate::elaborate::Shared;
use crate::grammar::chart::Budget;
use crate::grammar::math::{LeafKind, MathAst};
use crate::grammar::structural::AtomRange;
use crate::ir::term::{
    Binder, CoreRef, DefinedLexiconRef, DocumentDeclRef, ExternalConstRef, GlobalRef,
    ImplicitBinderId, LocalId, Term, Universe,
};
use crate::lexicon::entry::{Denotation, Entry};
use crate::lexicon::lse::{BinderMode, Lse, QualifiedId};
use crate::lexicon::resolve::FormRef;
use crate::source::atom::{Atom, AtomClass};
use crate::source::coverage::{Origin, SourceRow};

/// A metavariable store: term metas keyed by `LocalId`, universe metas by
/// generated name.
#[derive(Debug, Clone, Default)]
pub struct Metas {
    terms: BTreeMap<LocalId, Option<Term>>,
    universes: BTreeMap<String, Option<Universe>>,
}

impl Metas {
    fn fresh_term(&mut self, alloc: &mut LocalAlloc) -> LocalId {
        let id = alloc.fresh();
        self.terms.insert(id, None);
        id
    }

    fn fresh_universe(&mut self) -> String {
        let name = format!("?u{}", self.universes.len());
        self.universes.insert(name.clone(), None);
        name
    }

    fn is_meta(&self, id: LocalId) -> bool {
        self.terms.contains_key(&id)
    }

    fn lookup(&self, id: LocalId) -> Option<&Term> {
        self.terms.get(&id).and_then(Option::as_ref)
    }
}

/// One elaborated result.
#[derive(Debug, Clone)]
pub struct ElabTerm {
    /// The linked term, fully zonked.
    pub term: Term,
    /// The conservatively known type, `None` when unknown.
    pub ty: Option<Term>,
    /// Coverage rows for the selected interpretation.
    pub rows: Vec<SourceRow>,
}

#[derive(Debug, Clone)]
struct Cand {
    term: Term,
    ty: Term,
    metas: Metas,
    rows: Vec<SourceRow>,
}

/// The expression elaborator over one module context.
pub struct ExprElab<'a, 'b> {
    /// The shared module context.
    pub shared: &'b Shared<'a>,
    /// The lexical scopes.
    pub scopes: &'b ScopeStack,
    /// The local allocator.
    pub alloc: &'b mut LocalAlloc,
    /// The parse budget.
    pub budget: &'b mut Budget,
}

fn substitute(term: &Term, map: &BTreeMap<LocalId, Term>) -> Term {
    match term {
        Term::Local(id) => map.get(id).cloned().unwrap_or_else(|| term.clone()),
        Term::Sort(_) | Term::Global(..) => term.clone(),
        Term::App {
            function,
            explicit_args,
            omitted_implicit_binders,
        } => Term::App {
            function: Box::new(substitute(function, map)),
            explicit_args: explicit_args
                .iter()
                .map(|arg| substitute(arg, map))
                .collect(),
            omitted_implicit_binders: omitted_implicit_binders.clone(),
        },
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            let new_binders: Vec<Binder> = binders
                .iter()
                .map(|binder| Binder {
                    id: binder.id,
                    mode: binder.mode,
                    ty: substitute(&binder.ty, map),
                    spelling: binder.spelling.clone(),
                })
                .collect();
            let new_body = Box::new(substitute(body, map));
            if matches!(term, Term::Pi { .. }) {
                Term::Pi {
                    binders: new_binders,
                    body: new_body,
                }
            } else {
                Term::Lambda {
                    binders: new_binders,
                    body: new_body,
                }
            }
        }
        Term::Let {
            binder,
            value,
            body,
        } => Term::Let {
            binder: Box::new(Binder {
                id: binder.id,
                mode: binder.mode,
                ty: substitute(&binder.ty, map),
                spelling: binder.spelling.clone(),
            }),
            value: Box::new(substitute(value, map)),
            body: Box::new(substitute(body, map)),
        },
        Term::NatLiteral {
            decimal,
            expected_type,
        } => Term::NatLiteral {
            decimal: decimal.clone(),
            expected_type: Box::new(substitute(expected_type, map)),
        },
    }
}

/// Deep meta resolution.
fn zonk(term: &Term, metas: &Metas) -> Term {
    match term {
        Term::Local(id) => match metas.lookup(*id) {
            Some(solution) => zonk(solution, metas),
            None => term.clone(),
        },
        Term::Sort(universe) => Term::Sort(zonk_universe(universe, metas)),
        Term::Global(global, universes) => Term::Global(
            global.clone(),
            universes
                .iter()
                .map(|universe| zonk_universe(universe, metas))
                .collect(),
        ),
        Term::App {
            function,
            explicit_args,
            omitted_implicit_binders,
        } => Term::App {
            function: Box::new(zonk(function, metas)),
            explicit_args: explicit_args.iter().map(|arg| zonk(arg, metas)).collect(),
            omitted_implicit_binders: omitted_implicit_binders.clone(),
        },
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            let new_binders: Vec<Binder> = binders
                .iter()
                .map(|binder| Binder {
                    id: binder.id,
                    mode: binder.mode,
                    ty: zonk(&binder.ty, metas),
                    spelling: binder.spelling.clone(),
                })
                .collect();
            let new_body = Box::new(zonk(body, metas));
            if matches!(term, Term::Pi { .. }) {
                Term::Pi {
                    binders: new_binders,
                    body: new_body,
                }
            } else {
                Term::Lambda {
                    binders: new_binders,
                    body: new_body,
                }
            }
        }
        Term::Let {
            binder,
            value,
            body,
        } => Term::Let {
            binder: Box::new(Binder {
                id: binder.id,
                mode: binder.mode,
                ty: zonk(&binder.ty, metas),
                spelling: binder.spelling.clone(),
            }),
            value: Box::new(zonk(value, metas)),
            body: Box::new(zonk(body, metas)),
        },
        Term::NatLiteral {
            decimal,
            expected_type,
        } => Term::NatLiteral {
            decimal: decimal.clone(),
            expected_type: Box::new(zonk(expected_type, metas)),
        },
    }
}

fn zonk_universe(universe: &Universe, metas: &Metas) -> Universe {
    match universe {
        Universe::Var(name) => match metas.universes.get(name).and_then(Option::as_ref) {
            Some(solution) => zonk_universe(solution, metas),
            None => universe.clone(),
        },
        Universe::Num(_) => universe.clone(),
        Universe::Succ(inner) => normalize_succ(zonk_universe(inner, metas)),
        Universe::Max(items) => Universe::Max(
            items
                .iter()
                .map(|item| zonk_universe(item, metas))
                .collect(),
        ),
        Universe::IMax(a, b) => Universe::IMax(
            Box::new(zonk_universe(a, metas)),
            Box::new(zonk_universe(b, metas)),
        ),
    }
}

fn normalize_succ(universe: Universe) -> Universe {
    match universe {
        Universe::Num(n) => Universe::Num(n + 1),
        other => Universe::Succ(Box::new(other)),
    }
}

/// Erase universe argument lists that still carry unsolved universe metas:
/// universe instantiation is Lean's (§17.6 never claims kernel equivalence),
/// and generated Lean never prints universes (§18.4).
fn strip_unsolved_universes(term: &Term, metas: &Metas) -> Term {
    match term {
        Term::Global(global, universes) => {
            if universes
                .iter()
                .any(|universe| universe_unsolved(universe, metas))
            {
                Term::Global(global.clone(), Vec::new())
            } else {
                term.clone()
            }
        }
        Term::Local(_) | Term::Sort(_) => term.clone(),
        Term::App {
            function,
            explicit_args,
            omitted_implicit_binders,
        } => Term::App {
            function: Box::new(strip_unsolved_universes(function, metas)),
            explicit_args: explicit_args
                .iter()
                .map(|arg| strip_unsolved_universes(arg, metas))
                .collect(),
            omitted_implicit_binders: omitted_implicit_binders.clone(),
        },
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            let new_binders: Vec<Binder> = binders
                .iter()
                .map(|binder| Binder {
                    id: binder.id,
                    mode: binder.mode,
                    ty: strip_unsolved_universes(&binder.ty, metas),
                    spelling: binder.spelling.clone(),
                })
                .collect();
            let new_body = Box::new(strip_unsolved_universes(body, metas));
            if matches!(term, Term::Pi { .. }) {
                Term::Pi {
                    binders: new_binders,
                    body: new_body,
                }
            } else {
                Term::Lambda {
                    binders: new_binders,
                    body: new_body,
                }
            }
        }
        Term::Let {
            binder,
            value,
            body,
        } => Term::Let {
            binder: Box::new(Binder {
                id: binder.id,
                mode: binder.mode,
                ty: strip_unsolved_universes(&binder.ty, metas),
                spelling: binder.spelling.clone(),
            }),
            value: Box::new(strip_unsolved_universes(value, metas)),
            body: Box::new(strip_unsolved_universes(body, metas)),
        },
        Term::NatLiteral {
            decimal,
            expected_type,
        } => Term::NatLiteral {
            decimal: decimal.clone(),
            expected_type: Box::new(strip_unsolved_universes(expected_type, metas)),
        },
    }
}

fn has_unsolved(term: &Term, metas: &Metas) -> bool {
    match term {
        Term::Local(id) => metas.is_meta(*id) && metas.lookup(*id).is_none(),
        Term::Sort(universe) => universe_unsolved(universe, metas),
        Term::Global(_, universes) => universes
            .iter()
            .any(|universe| universe_unsolved(universe, metas)),
        Term::App {
            function,
            explicit_args,
            ..
        } => {
            has_unsolved(function, metas)
                || explicit_args.iter().any(|arg| has_unsolved(arg, metas))
        }
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            binders.iter().any(|binder| has_unsolved(&binder.ty, metas))
                || has_unsolved(body, metas)
        }
        Term::Let {
            binder,
            value,
            body,
        } => {
            has_unsolved(&binder.ty, metas)
                || has_unsolved(value, metas)
                || has_unsolved(body, metas)
        }
        Term::NatLiteral { expected_type, .. } => has_unsolved(expected_type, metas),
    }
}

fn universe_unsolved(universe: &Universe, metas: &Metas) -> bool {
    match universe {
        Universe::Var(name) => {
            metas.universes.contains_key(name)
                && metas.universes.get(name).and_then(Option::as_ref).is_none()
        }
        Universe::Num(_) => false,
        Universe::Succ(inner) => universe_unsolved(inner, metas),
        Universe::Max(items) => items.iter().any(|item| universe_unsolved(item, metas)),
        Universe::IMax(a, b) => universe_unsolved(a, metas) || universe_unsolved(b, metas),
    }
}

fn occurs(id: LocalId, term: &Term) -> bool {
    match term {
        Term::Local(other) => *other == id,
        Term::Sort(_) | Term::Global(..) => false,
        Term::App {
            function,
            explicit_args,
            ..
        } => occurs(id, function) || explicit_args.iter().any(|arg| occurs(id, arg)),
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            binders.iter().any(|binder| occurs(id, &binder.ty)) || occurs(id, body)
        }
        Term::Let {
            binder,
            value,
            body,
        } => occurs(id, &binder.ty) || occurs(id, value) || occurs(id, body),
        Term::NatLiteral { expected_type, .. } => occurs(id, expected_type),
    }
}

fn unify_universe(a: &Universe, b: &Universe, metas: &mut Metas) -> bool {
    let a = zonk_universe(a, metas);
    let b = zonk_universe(b, metas);
    match (&a, &b) {
        (Universe::Var(name), other) if metas.universes.contains_key(name) => {
            metas.universes.insert(name.clone(), Some(other.clone()));
            true
        }
        (other, Universe::Var(name)) if metas.universes.contains_key(name) => {
            metas.universes.insert(name.clone(), Some(other.clone()));
            true
        }
        (Universe::Num(x), Universe::Num(y)) => x == y,
        (Universe::Var(x), Universe::Var(y)) => x == y,
        (Universe::Succ(x), Universe::Succ(y)) => unify_universe(x, y, metas),
        (Universe::Succ(x), Universe::Num(n)) | (Universe::Num(n), Universe::Succ(x)) => {
            *n > 0 && unify_universe(x, &Universe::Num(n - 1), metas)
        }
        (Universe::Max(xs), Universe::Max(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| unify_universe(x, y, metas))
        }
        (Universe::IMax(x1, x2), Universe::IMax(y1, y2)) => {
            unify_universe(x1, y1, metas) && unify_universe(x2, y2, metas)
        }
        _ => false,
    }
}

/// Conservative unification: syntactic up to alpha, metas, and universe
/// normalization. Failure means the candidate dies; success never claims
/// Lean definitional equality (§17.6).
fn unify(a: &Term, b: &Term, metas: &mut Metas) -> bool {
    let a = zonk(a, metas);
    let b = zonk(b, metas);
    match (&a, &b) {
        (Term::Local(id), other) if metas.is_meta(*id) => {
            if let Term::Local(other_id) = other {
                if other_id == id {
                    return true;
                }
            }
            if occurs(*id, other) {
                return false;
            }
            metas.terms.insert(*id, Some(other.clone()));
            true
        }
        (other, Term::Local(id)) if metas.is_meta(*id) => {
            if occurs(*id, other) {
                return false;
            }
            metas.terms.insert(*id, Some(other.clone()));
            true
        }
        (Term::Local(x), Term::Local(y)) => x == y,
        (Term::Sort(x), Term::Sort(y)) => unify_universe(x, y, metas),
        (Term::Global(gx, ux), Term::Global(gy, uy)) => {
            if gx != gy {
                return false;
            }
            // A stripped side (empty universe list) matches any pending
            // metavariable list: strip_unsolved_universes erases arguments
            // that stayed generic, and conservative unification never
            // reintroduces them (§17.6).
            if ux.is_empty() || uy.is_empty() {
                return true;
            }
            ux.len() == uy.len() && ux.iter().zip(uy).all(|(x, y)| unify_universe(x, y, metas))
        }
        (
            Term::App {
                function: fx,
                explicit_args: ax,
                ..
            },
            Term::App {
                function: fy,
                explicit_args: ay,
                ..
            },
        ) => {
            ax.len() == ay.len()
                && unify(fx, fy, metas)
                && ax.iter().zip(ay).all(|(x, y)| unify(x, y, metas))
        }
        (
            Term::Pi {
                binders: bx,
                body: vx,
            },
            Term::Pi {
                binders: by,
                body: vy,
            },
        )
        | (
            Term::Lambda {
                binders: bx,
                body: vx,
            },
            Term::Lambda {
                binders: by,
                body: vy,
            },
        ) => {
            if bx.len() != by.len() {
                return false;
            }
            let mut rename: BTreeMap<LocalId, Term> = BTreeMap::new();
            for (x, y) in bx.iter().zip(by) {
                if x.mode != y.mode {
                    return false;
                }
                let y_ty = substitute(&y.ty, &rename);
                if !unify(&x.ty, &y_ty, metas) {
                    return false;
                }
                rename.insert(y.id, Term::Local(x.id));
            }
            let vy_renamed = substitute(vy, &rename);
            unify(vx, &vy_renamed, metas)
        }
        (
            Term::NatLiteral {
                decimal: dx,
                expected_type: tx,
            },
            Term::NatLiteral {
                decimal: dy,
                expected_type: ty,
            },
        ) => dx == dy && unify(tx, ty, metas),
        _ => false,
    }
}

/// Convert an entry's LSE (signature or defined value) to a `Term` with
/// fresh binder identities, resolving constants through the closure.
pub fn lse_to_term(
    lse: &Lse,
    shared: &Shared<'_>,
    alloc: &mut LocalAlloc,
    universe_map: &BTreeMap<String, Universe>,
) -> Result<Term, String> {
    fn universe_of(
        universe: &crate::lexicon::lse::Universe,
        map: &BTreeMap<String, Universe>,
    ) -> Universe {
        match universe {
            Universe::Num(n) => Universe::Num(*n),
            Universe::Var(name) => map
                .get(name)
                .cloned()
                .unwrap_or_else(|| Universe::Var(name.clone())),
            Universe::Succ(inner) => normalize_succ(universe_of(inner, map)),
            Universe::Max(items) => {
                Universe::Max(items.iter().map(|item| universe_of(item, map)).collect())
            }
            Universe::IMax(a, b) => {
                Universe::IMax(Box::new(universe_of(a, map)), Box::new(universe_of(b, map)))
            }
        }
    }
    fn walk(
        lse: &Lse,
        shared: &Shared<'_>,
        alloc: &mut LocalAlloc,
        scope: &mut Vec<(String, LocalId)>,
        map: &BTreeMap<String, Universe>,
    ) -> Result<Term, String> {
        Ok(match lse {
            Lse::SortProp => Term::Sort(Universe::Num(0)),
            Lse::SortType(universe) => Term::Sort(normalize_succ(universe_of(universe, map))),
            Lse::Const(id, universes) => {
                let global = global_for_entry(shared, id)?;
                Term::Global(
                    global,
                    universes
                        .iter()
                        .map(|universe| universe_of(universe, map))
                        .collect(),
                )
            }
            Lse::Local(name) => {
                let id = scope
                    .iter()
                    .rev()
                    .find(|(spelling, _)| spelling == name)
                    .map(|(_, id)| *id)
                    .ok_or_else(|| format!("local `{name}` is not in scope"))?;
                Term::Local(id)
            }
            Lse::App(function, arguments) => Term::App {
                function: Box::new(walk(function, shared, alloc, scope, map)?),
                explicit_args: arguments
                    .iter()
                    .map(|argument| walk(argument, shared, alloc, scope, map))
                    .collect::<Result<_, _>>()?,
                omitted_implicit_binders: Vec::new(),
            },
            Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
                let depth = scope.len();
                let mut ir_binders = Vec::new();
                for binder in binders {
                    let ty = walk(&binder.ty, shared, alloc, scope, map)?;
                    let id = alloc.fresh();
                    scope.push((binder.name.clone(), id));
                    ir_binders.push(Binder {
                        id,
                        mode: binder.mode,
                        ty,
                        spelling: binder.name.clone(),
                    });
                }
                let ir_body = Box::new(walk(body, shared, alloc, scope, map)?);
                scope.truncate(depth);
                if matches!(lse, Lse::Pi(..)) {
                    Term::Pi {
                        binders: ir_binders,
                        body: ir_body,
                    }
                } else {
                    Term::Lambda {
                        binders: ir_binders,
                        body: ir_body,
                    }
                }
            }
            Lse::Let {
                name,
                ty,
                value,
                body,
            } => {
                let ty_term = walk(ty, shared, alloc, scope, map)?;
                let value_term = walk(value, shared, alloc, scope, map)?;
                let id = alloc.fresh();
                scope.push((name.clone(), id));
                let body_term = walk(body, shared, alloc, scope, map)?;
                scope.pop();
                Term::Let {
                    binder: Box::new(Binder {
                        id,
                        mode: BinderMode::Explicit,
                        ty: ty_term,
                        spelling: name.clone(),
                    }),
                    value: Box::new(value_term),
                    body: Box::new(body_term),
                }
            }
            Lse::Nat(decimal) => {
                // A literal in glossary data carries no context; its type
                // must come from an enclosing application.
                let meta = alloc.fresh();
                Term::NatLiteral {
                    decimal: decimal.clone(),
                    expected_type: Box::new(Term::Local(meta)),
                }
            }
        })
    }
    walk(lse, shared, alloc, &mut Vec::new(), universe_map)
}

/// The `GlobalRef` for a glossary entry (§17.2). Document entries resolve
/// through the availability table (§17.7).
pub fn global_for_entry(shared: &Shared<'_>, id: &QualifiedId) -> Result<GlobalRef, String> {
    let entry = shared
        .closure
        .entry(id)
        .ok_or_else(|| format!("`{id}` is not in the glossary closure"))?;
    global_for(shared, id, entry)
}

fn global_for(shared: &Shared<'_>, id: &QualifiedId, entry: &Entry) -> Result<GlobalRef, String> {
    Ok(match &entry.denotation {
        Denotation::Core { constructor } => {
            let core = CoreRef::from_constructor(constructor).ok_or_else(|| {
                format!("core constructor `{constructor}` has no term denotation")
            })?;
            GlobalRef::Core(core)
        }
        Denotation::Lean { module, name } => GlobalRef::External(ExternalConstRef {
            package: id.package.clone(),
            entry: id.to_string(),
            lean_module: module.clone(),
            lean_name: name.clone(),
            signature_hash: entry
                .signature_hash
                .ok_or_else(|| format!("`{id}` has no signature"))?,
        }),
        Denotation::Document { module, component } => {
            let info = shared.decls.get(module, component).ok_or_else(|| {
                format!("document declaration `{module}::{component}` is not available here")
            })?;
            GlobalRef::Document(DocumentDeclRef {
                module: module.clone(),
                component: component.clone(),
                lean_name: info.lean_name.clone(),
            })
        }
        Denotation::Defined { .. } => GlobalRef::DefinedLexicon(DefinedLexiconRef {
            package: id.package.clone(),
            entry: id.to_string(),
            signature_hash: entry
                .signature_hash
                .ok_or_else(|| format!("`{id}` has no signature"))?,
        }),
    })
}

impl<'a, 'b> ExprElab<'a, 'b> {
    fn bytes_of(&self, range: AtomRange) -> (usize, usize) {
        let first = &self.shared.atoms[range.0];
        let last = &self.shared.atoms[range.1.saturating_sub(1).max(range.0)];
        (first.byte_start, last.byte_end)
    }

    fn row(&self, range: AtomRange, class: AtomClass, binding: Origin) -> SourceRow {
        let (byte_start, byte_end) = self.bytes_of(range);
        SourceRow {
            path: self.shared.path.to_owned(),
            byte_start,
            byte_end,
            class,
            binding,
        }
    }

    fn atom_row(&self, index: usize, binding: Origin) -> SourceRow {
        let atom: &Atom = &self.shared.atoms[index];
        SourceRow {
            path: self.shared.path.to_owned(),
            byte_start: atom.byte_start,
            byte_end: atom.byte_end,
            class: atom.class,
            binding,
        }
    }

    /// Instantiate an entry as a global with its signature type. Universe
    /// variables become fresh universe metas per use.
    fn instantiate_entry(
        &mut self,
        reference: &FormRef,
        metas: &mut Metas,
    ) -> Result<(Term, Term), String> {
        let qualified = QualifiedId {
            package: reference.package.clone(),
            entry: reference.entry.clone(),
        };
        let entry = self
            .shared
            .closure
            .entry(&qualified)
            .ok_or_else(|| format!("`{qualified}` is not in the glossary closure"))?;
        let signature = entry
            .signature
            .as_ref()
            .ok_or_else(|| format!("`{qualified}` has no signature"))?;
        let mut universe_map = BTreeMap::new();
        let mut universe_args = Vec::new();
        for name in &entry.universes {
            let fresh = self.alloc_universe(metas);
            universe_map.insert(name.clone(), fresh.clone());
            universe_args.push(fresh);
        }
        let ty = lse_to_term(signature, self.shared, self.alloc, &universe_map)?;
        let global = global_for(self.shared, &qualified, entry)?;
        Ok((Term::Global(global, universe_args), ty))
    }

    fn alloc_universe(&mut self, metas: &mut Metas) -> Universe {
        Universe::Var(metas.fresh_universe())
    }

    /// Apply a function candidate to arguments through its telescope,
    /// skipping implicit and instance binders into metas and recording them
    /// as omitted (§17.3, §17.6).
    fn apply(
        &mut self,
        function: Term,
        function_ty: Term,
        args: &[Cand],
        metas: &mut Metas,
    ) -> Option<(Term, Term)> {
        let mut remaining_ty = zonk(&function_ty, metas);
        let mut ordinal: u32 = 0;
        let mut omitted = Vec::new();
        let mut explicit_terms = Vec::new();
        let mut args_iter = args.iter();
        let mut pending: Option<&Cand> = args_iter.next();
        while pending.is_some() {
            let Term::Pi { binders, body } = remaining_ty else {
                return None;
            };
            let mut subst_map: BTreeMap<LocalId, Term> = BTreeMap::new();
            let mut consumed_all = true;
            let mut leftover: Vec<Binder> = Vec::new();
            let mut binder_iter = binders.into_iter();
            for binder in binder_iter.by_ref() {
                let binder_ty = substitute(&binder.ty, &subst_map);
                match binder.mode {
                    BinderMode::Implicit | BinderMode::Instance => {
                        let meta = metas.fresh_term(self.alloc);
                        // The meta's expected type is the binder type; the
                        // solution comes from unification with argument
                        // types.
                        let _ = binder_ty;
                        subst_map.insert(binder.id, Term::Local(meta));
                        omitted.push(ImplicitBinderId(ordinal));
                    }
                    BinderMode::Explicit => match pending {
                        Some(argument) => {
                            if let Some(arg_ty) = argument.ty_known(metas) {
                                if !unify(&arg_ty, &binder_ty, metas) {
                                    return None;
                                }
                            } else if !unify(&argument.ty.clone(), &binder_ty, metas) {
                                return None;
                            }
                            subst_map.insert(binder.id, argument.term.clone());
                            explicit_terms.push(argument.term.clone());
                            pending = args_iter.next();
                        }
                        None => {
                            // Arguments exhausted: the rest of this binder
                            // group is a leftover Pi.
                            leftover.push(Binder {
                                id: binder.id,
                                mode: binder.mode,
                                ty: binder_ty,
                                spelling: binder.spelling,
                            });
                            consumed_all = false;
                            break;
                        }
                    },
                }
                ordinal += 1;
            }
            if consumed_all {
                remaining_ty = zonk(&substitute(&body, &subst_map), metas);
            } else {
                for binder in binder_iter {
                    leftover.push(Binder {
                        id: binder.id,
                        mode: binder.mode,
                        ty: substitute(&binder.ty, &subst_map),
                        spelling: binder.spelling,
                    });
                }
                remaining_ty = Term::Pi {
                    binders: leftover,
                    body: Box::new(substitute(&body, &subst_map)),
                };
                break;
            }
        }
        let term = Term::App {
            function: Box::new(function),
            explicit_args: explicit_terms,
            omitted_implicit_binders: omitted,
        };
        Some((term, remaining_ty))
    }

    #[allow(clippy::too_many_lines)]
    fn candidates(&mut self, ast: &MathAst) -> Result<Vec<Cand>, Diagnostic> {
        self.budget.state()?;
        let mut out: Vec<Cand> = Vec::new();
        match ast {
            MathAst::Numeral { text, atoms } => {
                let mut metas = Metas::default();
                let meta = metas.fresh_term(self.alloc);
                let expected = Term::Local(meta);
                out.push(Cand {
                    term: Term::NatLiteral {
                        decimal: text.clone(),
                        expected_type: Box::new(expected.clone()),
                    },
                    ty: expected,
                    metas,
                    rows: vec![self.row(*atoms, AtomClass::Numeral, Origin::Numeral)],
                });
            }
            MathAst::Leaf { kinds, atoms } => {
                let mut last_instantiation_error: Option<Diagnostic> = None;
                for kind in kinds {
                    match kind {
                        LeafKind::Ident(spelling) => {
                            if let Some(entry) = self.scopes.lookup(spelling) {
                                let mut metas = Metas::default();
                                let ty = match &entry.ty {
                                    Some(known) => known.clone(),
                                    None => Term::Local(metas.fresh_term(self.alloc)),
                                };
                                out.push(Cand {
                                    term: Term::Local(entry.id),
                                    ty,
                                    metas,
                                    rows: vec![self.row(
                                        *atoms,
                                        AtomClass::Word,
                                        Origin::Local(entry.id.0 as usize),
                                    )],
                                });
                            }
                        }
                        LeafKind::Form(reference) => {
                            let mut metas = Metas::default();
                            match self.instantiate_entry(reference, &mut metas) {
                                Err(instantiation_error) => {
                                    let (byte_start, byte_end) = self.bytes_of(*atoms);
                                    let first = &self.shared.atoms[atoms.0];
                                    last_instantiation_error = Some(
                                        Diagnostic::new(code!("LLR3005"), instantiation_error)
                                            .with_span(crate::diagnostic::Span {
                                                path: self.shared.path.to_owned(),
                                                byte_start,
                                                byte_end,
                                                line_start: first.line_start,
                                                column_start: first.column_start,
                                                line_end: first.line_end,
                                                column_end: first.column_end,
                                            }),
                                    );
                                }
                                Ok((term, ty)) => {
                                    out.push(Cand {
                                        term,
                                        ty,
                                        metas,
                                        rows: vec![self.row(
                                            *atoms,
                                            self.shared.atoms[atoms.0].class,
                                            Origin::Form {
                                                package: reference.package.clone(),
                                                entry: reference.entry.clone(),
                                                form: reference.form.clone(),
                                            },
                                        )],
                                    });
                                }
                            }
                        }
                    }
                }
                if out.is_empty() {
                    // A form existed but could not instantiate: that failure
                    // is the diagnosis, not an unknown atom.
                    if let Some(instantiation_error) = last_instantiation_error {
                        return Err(instantiation_error);
                    }
                    let (byte_start, byte_end) = self.bytes_of(*atoms);
                    let first = &self.shared.atoms[atoms.0];
                    return Err(Diagnostic::new(
                        code!("LLL1004"),
                        format!(
                            "`{}` resolves to no scoped declaration or glossary entry",
                            self.shared.atoms[atoms.0].text
                        ),
                    )
                    .with_span(crate::diagnostic::Span {
                        path: self.shared.path.to_owned(),
                        byte_start,
                        byte_end,
                        line_start: first.line_start,
                        column_start: first.column_start,
                        line_end: first.line_end,
                        column_end: first.column_end,
                    }));
                }
            }
            MathAst::Lexeme { qualified, atoms } => {
                let parsed = QualifiedId::parse(qualified).map_err(|reason| {
                    Diagnostic::new(code!("LLR3005"), reason).with_span(self.span_of(*atoms))
                })?;
                if !self.shared.visible.contains(&parsed.package) {
                    return Err(Diagnostic::new(
                        code!("LLR3005"),
                        format!("package `{}` is not used by this module", parsed.package),
                    )
                    .with_span(self.span_of(*atoms)));
                }
                let reference = self
                    .shared
                    .closure
                    .entry(&parsed)
                    .map(|entry| FormRef {
                        package: parsed.package.clone(),
                        entry: parsed.entry.clone(),
                        form: entry
                            .forms
                            .first()
                            .map(|form| form.id.clone())
                            .unwrap_or_default(),
                    })
                    .ok_or_else(|| {
                        Diagnostic::new(
                            code!("LLR3005"),
                            format!("`{parsed}` is not in the glossary closure"),
                        )
                        .with_span(self.span_of(*atoms))
                    })?;
                let mut metas = Metas::default();
                let (term, ty) =
                    self.instantiate_entry(&reference, &mut metas)
                        .map_err(|reason| {
                            Diagnostic::new(code!("LLR3005"), reason)
                                .with_span(self.span_of(*atoms))
                        })?;
                let mut rows = vec![self.atom_row(
                    atoms.0,
                    Origin::Structural {
                        package: "lexlean.core".to_owned(),
                        entry: "lexeme".to_owned(),
                    },
                )];
                for index in atoms.0 + 1..atoms.1 {
                    let atom = &self.shared.atoms[index];
                    if atom.class == AtomClass::Whitespace {
                        continue;
                    }
                    if atom.class == AtomClass::Delimiter {
                        rows.push(self.atom_row(
                            index,
                            Origin::Structural {
                                package: "lexlean.core".to_owned(),
                                entry: if atom.text == "{" {
                                    "brace-open".to_owned()
                                } else {
                                    "brace-close".to_owned()
                                },
                            },
                        ));
                    } else {
                        rows.push(self.atom_row(
                            index,
                            Origin::Metadata {
                                owner: "lexlean.core::lexeme".to_owned(),
                            },
                        ));
                    }
                }
                out.push(Cand {
                    term,
                    ty,
                    metas,
                    rows,
                });
            }
            MathAst::Reference {
                module,
                component,
                atoms,
            } => {
                let info = self.shared.decls.get(module, component).ok_or_else(|| {
                    Diagnostic::new(
                        code!("LLR3005"),
                        format!("`{module}::{component}` is not an available document declaration"),
                    )
                    .with_span(self.span_of(*atoms))
                })?;
                let mut rows = vec![self.atom_row(
                    atoms.0,
                    Origin::Structural {
                        package: "lexlean.core".to_owned(),
                        entry: "reference".to_owned(),
                    },
                )];
                for index in atoms.0 + 1..atoms.1 {
                    let atom = &self.shared.atoms[index];
                    if atom.class == AtomClass::Whitespace {
                        continue;
                    }
                    if atom.class == AtomClass::Delimiter {
                        rows.push(self.atom_row(
                            index,
                            Origin::Structural {
                                package: "lexlean.core".to_owned(),
                                entry: if atom.text == "{" {
                                    "brace-open".to_owned()
                                } else {
                                    "brace-close".to_owned()
                                },
                            },
                        ));
                    } else {
                        rows.push(self.atom_row(
                            index,
                            Origin::Reference {
                                module: module.clone(),
                                component: component.clone(),
                            },
                        ));
                    }
                }
                out.push(Cand {
                    term: Term::Global(
                        GlobalRef::Document(DocumentDeclRef {
                            module: module.clone(),
                            component: component.clone(),
                            lean_name: info.lean_name.clone(),
                        }),
                        Vec::new(),
                    ),
                    ty: info.ty.clone(),
                    metas: Metas::default(),
                    rows,
                });
            }
            MathAst::Paren { inner, atoms } => {
                for mut candidate in self.candidates(inner)? {
                    candidate.rows.push(self.atom_row(
                        atoms.0,
                        Origin::Structural {
                            package: "lexlean.core".to_owned(),
                            entry: "paren-open".to_owned(),
                        },
                    ));
                    candidate.rows.push(self.atom_row(
                        atoms.1 - 1,
                        Origin::Structural {
                            package: "lexlean.core".to_owned(),
                            entry: "paren-close".to_owned(),
                        },
                    ));
                    out.push(candidate);
                }
            }
            MathAst::Call { head, args, atoms } => {
                let head_cands = self.candidates(head)?;
                let mut arg_cands: Vec<Vec<Cand>> = Vec::new();
                for arg in args {
                    arg_cands.push(self.candidates(arg)?);
                }
                // Structural rows for the call parentheses and separators.
                let mut structural_rows = Vec::new();
                for index in head.atoms().1..atoms.1 {
                    let atom = &self.shared.atoms[index];
                    match (atom.class, atom.text.as_str()) {
                        (AtomClass::Delimiter, "(") => structural_rows.push(self.atom_row(
                            index,
                            Origin::Structural {
                                package: "lexlean.core".to_owned(),
                                entry: "paren-open".to_owned(),
                            },
                        )),
                        (AtomClass::Delimiter, ")") => structural_rows.push(self.atom_row(
                            index,
                            Origin::Structural {
                                package: "lexlean.core".to_owned(),
                                entry: "paren-close".to_owned(),
                            },
                        )),
                        (AtomClass::AsciiSymbol, ",") => structural_rows.push(self.atom_row(
                            index,
                            Origin::Structural {
                                package: "lexlean.core".to_owned(),
                                entry: "comma".to_owned(),
                            },
                        )),
                        _ => {}
                    }
                }
                self.combine_application(&head_cands, &arg_cands, &structural_rows, &mut out)?;
            }
            MathAst::Prefix {
                candidates,
                op_atoms,
                arg,
            } => {
                let arg_cands = self.candidates(arg)?;
                self.operator_application(candidates, *op_atoms, &[arg_cands], &mut out)?;
            }
            MathAst::Postfix {
                candidates,
                op_atoms,
                arg,
            } => {
                let arg_cands = self.candidates(arg)?;
                self.operator_application(candidates, *op_atoms, &[arg_cands], &mut out)?;
            }
            MathAst::Infix {
                candidates,
                op_atoms,
                lhs,
                rhs,
            } => {
                let lhs_cands = self.candidates(lhs)?;
                let rhs_cands = self.candidates(rhs)?;
                self.operator_application(
                    candidates,
                    *op_atoms,
                    &[lhs_cands, rhs_cands],
                    &mut out,
                )?;
            }
        }
        Ok(out)
    }

    fn combine_application(
        &mut self,
        heads: &[Cand],
        args: &[Vec<Cand>],
        structural_rows: &[SourceRow],
        out: &mut Vec<Cand>,
    ) -> Result<(), Diagnostic> {
        let mut combos: Vec<(Cand, Vec<Cand>)> = heads
            .iter()
            .map(|head| (head.clone(), Vec::new()))
            .collect();
        for arg_alternatives in args {
            let mut grown = Vec::new();
            for (head, chosen) in &combos {
                for alternative in arg_alternatives {
                    self.budget.state()?;
                    let mut extended = chosen.clone();
                    extended.push(alternative.clone());
                    grown.push((head.clone(), extended));
                }
            }
            combos = grown;
        }
        for (head, chosen) in combos {
            let mut metas = head.metas.clone();
            for argument in &chosen {
                metas.terms.extend(argument.metas.terms.clone());
                metas.universes.extend(argument.metas.universes.clone());
            }
            if let Some((term, ty)) =
                self.apply(head.term.clone(), head.ty.clone(), &chosen, &mut metas)
            {
                let mut rows = head.rows.clone();
                for argument in &chosen {
                    rows.extend(argument.rows.clone());
                }
                rows.extend(structural_rows.iter().cloned());
                out.push(Cand {
                    term,
                    ty,
                    metas,
                    rows,
                });
            }
        }
        Ok(())
    }

    fn operator_application(
        &mut self,
        operators: &[FormRef],
        op_atoms: AtomRange,
        args: &[Vec<Cand>],
        out: &mut Vec<Cand>,
    ) -> Result<(), Diagnostic> {
        for reference in operators {
            let mut metas = Metas::default();
            let Ok((function, function_ty)) = self.instantiate_entry(reference, &mut metas) else {
                continue;
            };
            let op_row = self.row(
                op_atoms,
                self.shared.atoms[op_atoms.0].class,
                Origin::Form {
                    package: reference.package.clone(),
                    entry: reference.entry.clone(),
                    form: reference.form.clone(),
                },
            );
            let head = Cand {
                term: function,
                ty: function_ty,
                metas,
                rows: vec![op_row],
            };
            self.combine_application(&[head], args, &[], out)?;
        }
        Ok(())
    }

    fn span_of(&self, range: AtomRange) -> crate::diagnostic::Span {
        let first = &self.shared.atoms[range.0];
        let last = &self.shared.atoms[range.1.saturating_sub(1).max(range.0)];
        crate::diagnostic::Span {
            path: self.shared.path.to_owned(),
            byte_start: first.byte_start,
            byte_end: last.byte_end,
            line_start: first.line_start,
            column_start: first.column_start,
            line_end: last.line_end,
            column_end: last.column_end,
        }
    }

    /// Apply one entry to already-elaborated argument terms (predicate
    /// frames, §15.6). The result carries only the operator's own coverage
    /// row; the caller owns the argument rows.
    pub fn apply_entry_to_terms(
        &mut self,
        reference: &FormRef,
        surface_atoms: AtomRange,
        args: &[ElabTerm],
        expected: Option<&Term>,
    ) -> Result<ElabTerm, Diagnostic> {
        let mut metas = Metas::default();
        let (function, function_ty) =
            self.instantiate_entry(reference, &mut metas)
                .map_err(|reason| {
                    Diagnostic::new(code!("LLT4001"), reason).with_span(self.span_of(surface_atoms))
                })?;
        let arg_cands: Vec<Cand> = args
            .iter()
            .map(|argument| {
                let ty = match &argument.ty {
                    Some(known) => known.clone(),
                    None => Term::Local(metas.fresh_term(self.alloc)),
                };
                Cand {
                    term: argument.term.clone(),
                    ty,
                    metas: Metas::default(),
                    rows: Vec::new(),
                }
            })
            .collect();
        let Some((term, ty)) = self.apply(function, function_ty, &arg_cands, &mut metas) else {
            return Err(Diagnostic::new(
                code!("LLT4001"),
                "the arguments do not satisfy the declared signature",
            )
            .with_span(self.span_of(surface_atoms)));
        };
        if let Some(expected_ty) = expected {
            if !unify(&ty, expected_ty, &mut metas) {
                return Err(Diagnostic::new(
                    code!("LLT4001"),
                    "the applied entry does not produce the expected type",
                )
                .with_span(self.span_of(surface_atoms)));
            }
        }
        let term = strip_unsolved_universes(&zonk(&term, &metas), &metas);
        if has_unsolved(&term, &metas) {
            return Err(Diagnostic::new(
                code!("LLT4001"),
                "an implicit argument or numeral type stays undetermined",
            )
            .with_span(self.span_of(surface_atoms)));
        }
        let ty = strip_unsolved_universes(&zonk(&ty, &metas), &metas);
        let ty = if has_unsolved(&ty, &metas) {
            None
        } else {
            Some(ty)
        };
        let rows = vec![self.row(
            surface_atoms,
            self.shared.atoms[surface_atoms.0].class,
            Origin::Form {
                package: reference.package.clone(),
                entry: reference.entry.clone(),
                form: reference.form.clone(),
            },
        )];
        Ok(ElabTerm { term, ty, rows })
    }

    /// Elaborate one mathematical expression to a unique interpretation
    /// (I5): exactly one distinct linked IR survives, or elaboration fails.
    pub fn elaborate(
        &mut self,
        ast: &MathAst,
        expected: Option<&Term>,
    ) -> Result<ElabTerm, Diagnostic> {
        let candidates = self.candidates(ast)?;
        let candidate_count = candidates.len();
        let mut survivors: Vec<(String, ElabTerm)> = Vec::new();
        for mut candidate in candidates {
            if let Some(expected_ty) = expected {
                if !unify(&candidate.ty, expected_ty, &mut candidate.metas) {
                    continue;
                }
            }
            let term = strip_unsolved_universes(
                &zonk(&candidate.term, &candidate.metas),
                &candidate.metas,
            );
            if has_unsolved(&term, &candidate.metas) {
                continue;
            }
            let ty =
                strip_unsolved_universes(&zonk(&candidate.ty, &candidate.metas), &candidate.metas);
            let ty = if has_unsolved(&ty, &candidate.metas) {
                None
            } else {
                Some(ty)
            };
            let key = term.canonical_key();
            if !survivors.iter().any(|(existing, _)| *existing == key) {
                survivors.push((
                    key,
                    ElabTerm {
                        term,
                        ty,
                        rows: candidate.rows,
                    },
                ));
            }
        }
        match survivors.len() {
            1 => Ok(survivors.into_iter().next().expect("one survivor").1),
            0 if candidate_count > 1 => Err(Diagnostic::new(
                code!("LLT4002"),
                "no overloaded candidate satisfies the declared signatures and expected types",
            )
            .with_span(self.span_of(ast.atoms()))),
            0 => Err(Diagnostic::new(
                code!("LLT4001"),
                "no interpretation satisfies the declared signatures and expected types",
            )
            .with_span(self.span_of(ast.atoms()))),
            _ => {
                // §14.4: present the differentiating qualified candidate IDs.
                let id_sets: Vec<std::collections::BTreeSet<String>> = survivors
                    .iter()
                    .map(|(_, elaborated)| {
                        let mut ids = std::collections::BTreeSet::new();
                        crate::elaborate::collect_global_ids(&elaborated.term, &mut ids);
                        ids
                    })
                    .collect();
                let union: std::collections::BTreeSet<String> =
                    id_sets.iter().flatten().cloned().collect();
                let differing: Vec<String> = union
                    .iter()
                    .filter(|id| !id_sets.iter().all(|set| set.contains(*id)))
                    .cloned()
                    .collect();
                let candidates = if differing.is_empty() {
                    union.into_iter().collect::<Vec<_>>().join(", ")
                } else {
                    differing.join(", ")
                };
                Err(Diagnostic::new(
                    code!("LLP2002"),
                    format!(
                        "{} distinct linked interpretations survive; the differentiating candidates are: {candidates}",
                        survivors.len()
                    ),
                )
                .with_span(self.span_of(ast.atoms())))
            }
        }
    }
}

impl Cand {
    fn ty_known(&self, metas: &Metas) -> Option<Term> {
        let ty = zonk(&self.ty, metas);
        if has_unsolved(&ty, metas) {
            None
        } else {
            Some(ty)
        }
    }
}

/// Beta-reduce one application of a lambda to one argument, for witness
/// goals (§16.2).
#[must_use]
pub fn beta1(function: &Term, argument: &Term) -> Term {
    if let Term::Lambda { binders, body } = function {
        if let Some((first, rest)) = binders.split_first() {
            let mut map = BTreeMap::new();
            map.insert(first.id, argument.clone());
            let new_body = substitute(body, &map);
            if rest.is_empty() {
                return new_body;
            }
            return Term::Lambda {
                binders: rest
                    .iter()
                    .map(|binder| Binder {
                        id: binder.id,
                        mode: binder.mode,
                        ty: substitute(&binder.ty, &map),
                        spelling: binder.spelling.clone(),
                    })
                    .collect(),
                body: Box::new(new_body),
            };
        }
    }
    Term::App {
        function: Box::new(function.clone()),
        explicit_args: vec![argument.clone()],
        omitted_implicit_binders: Vec::new(),
    }
}

/// Substitute a map of locals; public for the definition and proof
/// elaborators.
#[must_use]
pub fn subst(term: &Term, map: &BTreeMap<LocalId, Term>) -> Term {
    substitute(term, map)
}
