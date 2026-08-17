//! Conservative delta unfolding (SPEC.md §16.1, §17.6, §17.7): the one
//! place that reads a definition through its value. It sees through document
//! declarations (via the availability table, §17.7) and defined lexicon
//! values (§13.6), recursively — at the head and inside arguments and
//! binders — and reads unique existence as its §18.4 lowering, so every
//! expected-type comparison and every goal-shape check sees exactly what
//! pinned Lean sees when it unfolds a definition. Unfolding never claims
//! kernel equivalence: it only widens what conservative unification can
//! reconcile, and the shape predicates below say which mismatches no
//! unfolding can repair.

use std::collections::BTreeMap;

use crate::elaborate::expressions::{lse_to_term, subst, universe_map};
use crate::elaborate::resolve::LocalAlloc;
use crate::elaborate::Shared;
use crate::ir::term::{Binder, CoreRef, GlobalRef, ImplicitBinderId, LocalId, Term, Universe};
use crate::lexicon::entry::Denotation;
use crate::lexicon::lse::{BinderMode, QualifiedId};

/// Unfold every definition in `term`: a document declaration whose value
/// is available, or a defined lexicon value, applied to at least its
/// binders, is replaced by its instantiated value; a lambda head is
/// beta-reduced; unique existence is expanded to its lowering. The walk is
/// recursive so definitions inside arguments and binder types unfold too.
/// Definitions are acyclic (§13.6, §15.7 rule 8) and every unfolding
/// consumes one head; `limit` (the configured nesting limit) guards the
/// head loop against a linked table deeper than any source could be.
#[must_use]
pub fn unfold(term: &Term, shared: &Shared<'_>, alloc: &mut LocalAlloc, limit: u64) -> Term {
    let mut current = term.clone();
    let mut steps: u64 = 0;
    // The head loop: unfold or beta-reduce the head until it is rigid.
    while steps <= limit {
        let Some(next) = unfold_head(&current, shared, alloc) else {
            break;
        };
        current = next;
        steps = steps.saturating_add(1);
    }
    if let Term::App {
        function,
        explicit_args,
        ..
    } = &current
    {
        if let (
            Term::Global(GlobalRef::Core(CoreRef::ExistsUnique), _),
            [Term::Lambda { binders, body }],
        ) = (&**function, explicit_args.as_slice())
        {
            if let [binder] = binders.as_slice() {
                current = expand_exists_unique(binder, body, alloc);
            }
        }
    }
    match &current {
        Term::App {
            function,
            explicit_args,
            omitted_implicit_binders,
        } => Term::App {
            function: Box::new(unfold(function, shared, alloc, limit)),
            explicit_args: explicit_args
                .iter()
                .map(|argument| unfold(argument, shared, alloc, limit))
                .collect(),
            omitted_implicit_binders: omitted_implicit_binders.clone(),
        },
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            let new_binders = binders
                .iter()
                .map(|binder| Binder {
                    id: binder.id,
                    mode: binder.mode,
                    ty: unfold(&binder.ty, shared, alloc, limit),
                    spelling: binder.spelling.clone(),
                })
                .collect();
            let new_body = Box::new(unfold(body, shared, alloc, limit));
            if matches!(current, Term::Pi { .. }) {
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
                ty: unfold(&binder.ty, shared, alloc, limit),
                spelling: binder.spelling.clone(),
            }),
            value: Box::new(unfold(value, shared, alloc, limit)),
            body: Box::new(unfold(body, shared, alloc, limit)),
        },
        Term::NatLiteral {
            decimal,
            expected_type,
        } => Term::NatLiteral {
            decimal: decimal.clone(),
            expected_type: Box::new(unfold(expected_type, shared, alloc, limit)),
        },
        Term::Sort(_) | Term::Local(_) | Term::Global(..) => current,
    }
}

/// One head step: the definition value applied to the explicit arguments,
/// or a lambda head beta-reduced. `None` when the head is rigid (a local,
/// a core connective, an external constant, a theorem, a sort, a numeral)
/// or the definition is applied to fewer arguments than its binders.
fn unfold_head(term: &Term, shared: &Shared<'_>, alloc: &mut LocalAlloc) -> Option<Term> {
    let (function, args): (&Term, &[Term]) = match term {
        Term::App {
            function,
            explicit_args,
            ..
        } => (function, explicit_args),
        other => (other, &[]),
    };
    let value = match function {
        Term::Lambda { .. } if !args.is_empty() => return Some(beta(function, args)),
        Term::Global(GlobalRef::Document(reference), _) => {
            let info = shared.decls.get(&reference.module, &reference.component)?;
            fresh_binders(info.value.as_ref()?, alloc)
        }
        Term::Global(GlobalRef::DefinedLexicon(defined), universes) => {
            let id = QualifiedId::parse(&defined.entry).ok()?;
            let entry = shared.closure.entry(&id)?;
            let Denotation::Defined { value: lse, .. } = &entry.denotation else {
                return None;
            };
            let map = universe_map(&entry.universes, |index, name| {
                universes
                    .get(index)
                    .cloned()
                    .unwrap_or_else(|| Universe::Var(name.to_owned()))
            });
            lse_to_term(lse, shared, alloc, &map, None).ok()?
        }
        _ => return None,
    };
    Some(match value {
        Term::Lambda { binders, body } => {
            if args.len() < binders.len() {
                return None;
            }
            beta(&Term::Lambda { binders, body }, args)
        }
        other => apply(other, args),
    })
}

/// Beta-reduce a lambda applied to explicit arguments: the binders are
/// substituted by the arguments in order; leftover binders stay a lambda,
/// leftover arguments stay applied (§16.2 witness goals, §16.8 constructor
/// fields, definition unfolding).
#[must_use]
pub fn beta(function: &Term, args: &[Term]) -> Term {
    let Term::Lambda { binders, body } = function else {
        return apply(function.clone(), args);
    };
    let consumed = binders.len().min(args.len());
    let map: BTreeMap<LocalId, Term> = binders
        .iter()
        .zip(args)
        .map(|(binder, argument)| (binder.id, argument.clone()))
        .collect();
    let new_body = subst(body, &map);
    let reduced = if consumed == binders.len() {
        new_body
    } else {
        Term::Lambda {
            binders: binders[consumed..]
                .iter()
                .map(|binder| Binder {
                    id: binder.id,
                    mode: binder.mode,
                    ty: subst(&binder.ty, &map),
                    spelling: binder.spelling.clone(),
                })
                .collect(),
            body: Box::new(new_body),
        }
    };
    apply(reduced, &args[consumed..])
}

fn apply(function: Term, args: &[Term]) -> Term {
    if args.is_empty() {
        return function;
    }
    Term::App {
        function: Box::new(function),
        explicit_args: args.to_vec(),
        omitted_implicit_binders: Vec::new(),
    }
}

/// The §18.4 lowering of unique existence, given the bound binder and body
/// of `ExistsUnique (fun x => P)`:
/// `Exists (fun (x : T) => And P ((y : T) → P[x:=y] → Eq y x))`. The
/// proof elaborator reads unique existence through this expansion, exactly
/// as the Lean backend prints it, so a witness leaves the conjunction as
/// its residual goal.
#[must_use]
pub fn expand_exists_unique(binder: &Binder, body: &Term, alloc: &mut LocalAlloc) -> Term {
    let core = |core: CoreRef, args: Vec<Term>, omitted: Vec<ImplicitBinderId>| Term::App {
        function: Box::new(Term::Global(GlobalRef::Core(core), Vec::new())),
        explicit_args: args,
        omitted_implicit_binders: omitted,
    };
    let y = alloc.fresh();
    let mut rename = BTreeMap::new();
    rename.insert(binder.id, Term::Local(y));
    let holds_y = subst(body, &rename);
    let equal = core(
        CoreRef::Eq,
        vec![Term::Local(y), Term::Local(binder.id)],
        vec![ImplicitBinderId(0)],
    );
    let uniqueness = Term::Pi {
        binders: vec![Binder {
            id: y,
            mode: BinderMode::Explicit,
            ty: binder.ty.clone(),
            spelling: "y".to_owned(),
        }],
        body: Box::new(Term::Pi {
            binders: vec![Binder {
                id: alloc.fresh(),
                mode: BinderMode::Explicit,
                ty: holds_y,
                spelling: String::new(),
            }],
            body: Box::new(equal),
        }),
    };
    let conjunction = core(CoreRef::And, vec![body.clone(), uniqueness], Vec::new());
    core(
        CoreRef::Exists,
        vec![Term::Lambda {
            binders: vec![binder.clone()],
            body: Box::new(conjunction),
        }],
        vec![ImplicitBinderId(0)],
    )
}

/// A copy of `term` whose bound binders carry fresh identities, so one
/// definition value unfolded twice in one term never shares a binder
/// identity between the copies (I9).
fn fresh_binders(term: &Term, alloc: &mut LocalAlloc) -> Term {
    fn go(term: &Term, alloc: &mut LocalAlloc, map: &mut BTreeMap<LocalId, Term>) -> Term {
        match term {
            Term::Local(id) => map.get(id).cloned().unwrap_or_else(|| term.clone()),
            Term::Sort(_) | Term::Global(..) => term.clone(),
            Term::App {
                function,
                explicit_args,
                omitted_implicit_binders,
            } => Term::App {
                function: Box::new(go(function, alloc, map)),
                explicit_args: explicit_args
                    .iter()
                    .map(|argument| go(argument, alloc, map))
                    .collect(),
                omitted_implicit_binders: omitted_implicit_binders.clone(),
            },
            Term::Pi { binders, body } | Term::Lambda { binders, body } => {
                let new_binders: Vec<Binder> = binders
                    .iter()
                    .map(|binder| {
                        let ty = go(&binder.ty, alloc, map);
                        let id = alloc.fresh();
                        map.insert(binder.id, Term::Local(id));
                        Binder {
                            id,
                            mode: binder.mode,
                            ty,
                            spelling: binder.spelling.clone(),
                        }
                    })
                    .collect();
                let new_body = Box::new(go(body, alloc, map));
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
            } => {
                let ty = go(&binder.ty, alloc, map);
                let value = Box::new(go(value, alloc, map));
                let id = alloc.fresh();
                map.insert(binder.id, Term::Local(id));
                Term::Let {
                    binder: Box::new(Binder {
                        id,
                        mode: binder.mode,
                        ty,
                        spelling: binder.spelling.clone(),
                    }),
                    value,
                    body: Box::new(go(body, alloc, map)),
                }
            }
            Term::NatLiteral {
                decimal,
                expected_type,
            } => Term::NatLiteral {
                decimal: decimal.clone(),
                expected_type: Box::new(go(expected_type, alloc, map)),
            },
        }
    }
    go(term, alloc, &mut BTreeMap::new())
}

/// The coarse shape of a type for certain-mismatch detection: only shapes
/// that no definitional unfolding can turn into one another are compared.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeShape {
    /// A function type.
    Pi,
    /// A sort.
    Sort,
    /// An application of a core connective (unique existence reads as
    /// existence, its lowering).
    Core(CoreRef),
    /// Anything else (a local, an external constant, a definition, a
    /// numeral, ...): it may unfold to any shape.
    Open,
}

/// The shape of a (possibly unfolded) type.
#[must_use]
pub fn type_shape(term: &Term) -> TypeShape {
    let core = |core: &CoreRef| match core {
        CoreRef::ExistsUnique => TypeShape::Core(CoreRef::Exists),
        other => TypeShape::Core(*other),
    };
    match term {
        Term::Pi { .. } => TypeShape::Pi,
        Term::Sort(_) => TypeShape::Sort,
        Term::App { function, .. } => match &**function {
            Term::Global(GlobalRef::Core(c), _) => core(c),
            _ => TypeShape::Open,
        },
        Term::Global(GlobalRef::Core(c), _) => core(c),
        _ => TypeShape::Open,
    }
}

/// Is the shape of this type closed: a function type, a sort, or a core
/// connective, whose exact shape LexLean checks? Every other head (a
/// document or external predicate that may unfold) defers to Lean (§16.1).
#[must_use]
pub fn is_closed_shape(term: &Term) -> bool {
    type_shape(term) != TypeShape::Open
}

/// Are two types certainly distinct: both of a closed shape and of shapes
/// no unfolding can reconcile? Anything involving an open shape may still
/// be definitionally equal in Lean; `Not P` is `P → False`, so a negation
/// and a function type may coincide.
#[must_use]
pub fn certainly_distinct(a: &Term, b: &Term) -> bool {
    let (sa, sb) = (type_shape(a), type_shape(b));
    if sa == TypeShape::Open || sb == TypeShape::Open || sa == sb {
        return false;
    }
    !matches!(
        (sa, sb),
        (TypeShape::Pi, TypeShape::Core(CoreRef::Not))
            | (TypeShape::Core(CoreRef::Not), TypeShape::Pi)
    )
}
