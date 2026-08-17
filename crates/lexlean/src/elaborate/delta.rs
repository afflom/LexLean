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

use crate::diagnostic::{Diagnostic, Span};
use crate::elaborate::expressions::{lse_to_term, subst, universe_map};
use crate::elaborate::resolve::LocalAlloc;
use crate::elaborate::Shared;
use crate::grammar::chart::Budget;
use crate::ir::term::{Binder, CoreRef, GlobalRef, ImplicitBinderId, LocalId, Term, Universe};
use crate::lexicon::entry::Denotation;
use crate::lexicon::lse::{BinderMode, QualifiedId};

/// The phase every unfolding limit failure names (§25.5). Unfolding is the
/// one elaboration step whose output can be larger than its input, so it is
/// the phase a `max_ir_nodes` failure most often reports.
const PHASE: &str = "elaborate (definition unfolding)";

/// Unfold every definition in `term`: a document declaration whose value
/// is available, or a defined lexicon value, applied to at least its
/// binders, is replaced by its instantiated value; a lambda head is
/// beta-reduced; unique existence is expanded to its lowering. The walk is
/// recursive so definitions inside arguments and binder types unfold too.
/// Definitions are acyclic (§13.6, §15.7 rule 8) and every unfolding
/// consumes one head.
///
/// Nested definitions multiply: unfolding a definition whose value mentions
/// another definition several times is exponential in the nesting, so size
/// is a resource and not a property of the source's length. Every node this
/// function is about to allocate --- each head step, each rebuilt node ---
/// is therefore charged against `max_ir_nodes` *before* it is allocated
/// (§25.5), and the depth of the walk is charged against `max_scope_depth`,
/// so a nest of definitions is `LLS8002` naming the limit rather than an
/// allocation abort or an overflowed stack (§6 I14).
pub fn unfold(
    term: &Term,
    shared: &Shared<'_>,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
) -> Result<Term, Diagnostic> {
    unfold_at(term, shared, alloc, budget, 1).map_err(|mut diagnostic| {
        // The limit concerns the module being elaborated; a caller with a
        // finer span replaces this one.
        if diagnostic.primary.is_none() {
            diagnostic.primary = Some(Span::whole_file(shared.path));
        }
        diagnostic
    })
}

fn unfold_at(
    term: &Term,
    shared: &Shared<'_>,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    depth: u64,
) -> Result<Term, Diagnostic> {
    budget.depth(depth, PHASE)?;
    let limit = budget.max_depth();
    // The head loop: unfold or beta-reduce the head until it is rigid. The
    // term is copied only once a step actually fires, so reading a rigid
    // head --- by far the common case, and every leaf of the walk below ---
    // allocates nothing.
    let mut reduced: Option<Term> = None;
    let mut steps: u64 = 0;
    while steps <= limit {
        let head = reduced.as_ref().unwrap_or(term);
        let Some(next) = unfold_head(head, shared, alloc, budget)? else {
            break;
        };
        reduced = Some(next);
        steps = steps.saturating_add(1);
    }
    if let Term::App {
        function,
        explicit_args,
        ..
    } = reduced.as_ref().unwrap_or(term)
    {
        if let (
            Term::Global(GlobalRef::Core(CoreRef::ExistsUnique), _),
            [Term::Lambda { binders, body }],
        ) = (&**function, explicit_args.as_slice())
        {
            if let [binder] = binders.as_slice() {
                budget.ir_nodes(exists_unique_size(binder, body), PHASE)?;
                let expanded = expand_exists_unique(binder, body, alloc);
                reduced = Some(expanded);
            }
        }
    }
    let current = reduced.as_ref().unwrap_or(term);
    let next = depth.saturating_add(1);
    budget.ir_nodes(1, PHASE)?;
    Ok(match current {
        Term::App {
            function,
            explicit_args,
            omitted_implicit_binders,
        } => Term::App {
            function: Box::new(unfold_at(function, shared, alloc, budget, next)?),
            explicit_args: explicit_args
                .iter()
                .map(|argument| unfold_at(argument, shared, alloc, budget, next))
                .collect::<Result<Vec<Term>, Diagnostic>>()?,
            omitted_implicit_binders: omitted_implicit_binders.clone(),
        },
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            let new_binders = binders
                .iter()
                .map(|binder| {
                    Ok(Binder {
                        id: binder.id,
                        mode: binder.mode,
                        ty: unfold_at(&binder.ty, shared, alloc, budget, next)?,
                        spelling: binder.spelling.clone(),
                    })
                })
                .collect::<Result<Vec<Binder>, Diagnostic>>()?;
            let new_body = Box::new(unfold_at(body, shared, alloc, budget, next)?);
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
                ty: unfold_at(&binder.ty, shared, alloc, budget, next)?,
                spelling: binder.spelling.clone(),
            }),
            value: Box::new(unfold_at(value, shared, alloc, budget, next)?),
            body: Box::new(unfold_at(body, shared, alloc, budget, next)?),
        },
        Term::NatLiteral {
            decimal,
            expected_type,
        } => Term::NatLiteral {
            decimal: decimal.clone(),
            expected_type: Box::new(unfold_at(expected_type, shared, alloc, budget, next)?),
        },
        Term::Sort(_) | Term::Local(_) | Term::Global(..) => current.clone(),
    })
}

/// One head step: the definition value applied to the explicit arguments,
/// or a lambda head beta-reduced. `None` when the head is rigid (a local,
/// a core connective, an external constant, a theorem, a sort, a numeral)
/// or the definition is applied to fewer arguments than its binders.
fn unfold_head(
    term: &Term,
    shared: &Shared<'_>,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
) -> Result<Option<Term>, Diagnostic> {
    let (function, args): (&Term, &[Term]) = match term {
        Term::App {
            function,
            explicit_args,
            ..
        } => (function, explicit_args),
        other => (other, &[]),
    };
    let value = match function {
        Term::Lambda { .. } if !args.is_empty() => {
            return beta(function, args, budget).map(Some);
        }
        Term::Global(GlobalRef::Document(reference), _) => {
            let Some(info) = shared.decls.get(&reference.module, &reference.component) else {
                return Ok(None);
            };
            let Some(value) = info.value.as_ref() else {
                return Ok(None);
            };
            // `fresh_binders` copies the declaration value node for node.
            budget.ir_nodes(value.node_count(), PHASE)?;
            fresh_binders(value, alloc)
        }
        Term::Global(GlobalRef::DefinedLexicon(defined), universes) => {
            let Ok(id) = QualifiedId::parse(&defined.entry) else {
                return Ok(None);
            };
            let Some(entry) = shared.closure.entry(&id) else {
                return Ok(None);
            };
            let Denotation::Defined { value: lse, .. } = &entry.denotation else {
                return Ok(None);
            };
            let map = universe_map(&entry.universes, |index, name| {
                universes
                    .get(index)
                    .cloned()
                    .unwrap_or_else(|| Universe::Var(name.to_owned()))
            });
            let Ok(value) = lse_to_term(lse, shared, alloc, &map, None) else {
                return Ok(None);
            };
            // A lexicon value's size is bounded by the loaded entry rather
            // than by the term being unfolded, so it is charged once built.
            budget.ir_nodes(value.node_count(), PHASE)?;
            value
        }
        _ => return Ok(None),
    };
    Ok(Some(match value {
        Term::Lambda { binders, body } => {
            if args.len() < binders.len() {
                return Ok(None);
            }
            beta(&Term::Lambda { binders, body }, args, budget)?
        }
        other => {
            budget.ir_nodes(apply_size(args), PHASE)?;
            apply(other, args)
        }
    }))
}

/// Beta-reduce a lambda applied to explicit arguments: the binders are
/// substituted by the arguments in order; leftover binders stay a lambda,
/// leftover arguments stay applied (§16.2 witness goals, §16.8 constructor
/// fields, definition unfolding). Substitution copies each argument once per
/// occurrence of its binder, so the result is charged against `max_ir_nodes`
/// before it is built (§25.5).
pub fn beta(function: &Term, args: &[Term], budget: &mut Budget) -> Result<Term, Diagnostic> {
    let Term::Lambda { binders, body } = function else {
        budget.ir_nodes(
            function.node_count().saturating_add(apply_size(args)),
            PHASE,
        )?;
        return Ok(apply(function.clone(), args));
    };
    let consumed = binders.len().min(args.len());
    let sizes: BTreeMap<LocalId, u64> = binders
        .iter()
        .zip(args)
        .map(|(binder, argument)| (binder.id, argument.node_count()))
        .collect();
    let mut produced = subst_size(body, &sizes);
    if consumed < binders.len() {
        produced = binders[consumed..]
            .iter()
            .fold(produced.saturating_add(1), |total, binder| {
                total.saturating_add(subst_size(&binder.ty, &sizes))
            });
    }
    budget.ir_nodes(
        produced.saturating_add(apply_size(&args[consumed..])),
        PHASE,
    )?;
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
    Ok(apply(reduced, &args[consumed..]))
}

/// The node count [`subst`] would produce for `term` under a substitution
/// whose replacements have the given sizes: the same walk `subst` performs,
/// counting instead of allocating, so a substitution is charged before it
/// runs. Iterative, so measuring never costs stack the walk itself would
/// not.
fn subst_size(term: &Term, sizes: &BTreeMap<LocalId, u64>) -> u64 {
    let mut total: u64 = 0;
    let mut stack: Vec<&Term> = vec![term];
    while let Some(term) = stack.pop() {
        match term {
            Term::Local(id) => {
                total = total.saturating_add(sizes.get(id).copied().unwrap_or(1));
            }
            Term::Sort(_) | Term::Global(..) => total = total.saturating_add(1),
            Term::App {
                function,
                explicit_args,
                ..
            } => {
                total = total.saturating_add(1);
                stack.push(function);
                stack.extend(explicit_args.iter());
            }
            Term::Pi { binders, body } | Term::Lambda { binders, body } => {
                total = total.saturating_add(1);
                stack.extend(binders.iter().map(|binder| &binder.ty));
                stack.push(body);
            }
            Term::Let {
                binder,
                value,
                body,
            } => {
                total = total.saturating_add(1);
                stack.push(&binder.ty);
                stack.push(value);
                stack.push(body);
            }
            Term::NatLiteral { expected_type, .. } => {
                total = total.saturating_add(1);
                stack.push(expected_type);
            }
        }
    }
    total
}

/// The nodes [`apply`] allocates: the application node and one copy of each
/// argument. Applying nothing allocates nothing.
fn apply_size(args: &[Term]) -> u64 {
    if args.is_empty() {
        return 0;
    }
    args.iter()
        .map(Term::node_count)
        .fold(1, u64::saturating_add)
}

/// The nodes [`expand_exists_unique`] allocates for a binder of type `ty`
/// and body `body`: the body twice (the conjunct and the renamed
/// hypothesis), the binder type twice (the existential binder and the
/// uniqueness binder), and the eleven fixed nodes of the lowering.
fn exists_unique_size(binder: &Binder, body: &Term) -> u64 {
    body.node_count()
        .saturating_mul(2)
        .saturating_add(binder.ty.node_count().saturating_mul(2))
        .saturating_add(11)
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
