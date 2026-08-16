//! Conservative type-directed elaboration (SPEC.md §17.6): candidates are
//! filtered by scope, arity, categories, signatures, and conservative
//! unification; LexLean rejects rather than guesses (I5) and never claims
//! Lean definitional equality.

pub mod definitions;
pub mod expressions;
pub mod proofs;
pub mod resolve;

use std::collections::BTreeSet;

use crate::ir::term::Term;
use crate::lexicon::resolve::Closure;
use crate::source::atom::Atom;

/// One available document declaration (§17.7): declarations are available
/// only after their source position, and imported modules expose all their
/// exported declarations.
#[derive(Debug, Clone)]
pub struct DeclInfo {
    /// The source module.
    pub module: String,
    /// The component ID.
    pub component: String,
    /// The full generated Lean name.
    pub lean_name: String,
    /// The declaration's type: the statement for theorem-like kinds, the
    /// explicit type for definitions.
    pub ty: Term,
}

/// The table of available declarations, in availability order.
#[derive(Debug, Clone, Default)]
pub struct DeclTable {
    /// The rows.
    pub rows: Vec<DeclInfo>,
}

impl DeclTable {
    /// Look up a declaration.
    #[must_use]
    pub fn get(&self, module: &str, component: &str) -> Option<&DeclInfo> {
        self.rows
            .iter()
            .find(|row| row.module == module && row.component == component)
    }
}

/// The immutable per-module elaboration context.
pub struct Shared<'a> {
    /// The display path of the module source.
    pub path: &'a str,
    /// The scanned atoms.
    pub atoms: &'a [Atom],
    /// The glossary closure.
    pub closure: &'a Closure,
    /// The packages visible to this module.
    pub visible: &'a BTreeSet<String>,
    /// The declarations available so far.
    pub decls: &'a DeclTable,
    /// The current module name.
    pub module: &'a str,
    /// The module prefix, for generated names.
    pub module_prefix: &'a str,
}

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::elaborate::expressions::{ElabTerm, ExprElab};
use crate::elaborate::resolve::{LocalAlloc, ScopeStack};
use crate::grammar::chart::{Budget, TextToken};
use crate::grammar::math::parse_math;
use crate::grammar::proposition::{BinderAst, Keyword, PropAst, TermPhraseAst, TypePhraseAst};
use crate::ir::term::{Binder, CoreRef, GlobalRef, ImplicitBinderId};
use crate::lexicon::lse::BinderMode;
use crate::source::atom::AtomClass;
use crate::source::coverage::{Origin, SourceRow};

fn structural_row(shared: &Shared<'_>, atom: usize, entry: &str) -> SourceRow {
    let a = &shared.atoms[atom];
    SourceRow {
        path: shared.path.to_owned(),
        byte_start: a.byte_start,
        byte_end: a.byte_end,
        class: a.class,
        binding: Origin::Structural {
            package: "lexlean.core".to_owned(),
            entry: entry.to_owned(),
        },
    }
}

/// Coverage rows for a math island's delimiting controls; public for the
/// proof elaborator.
pub fn island_delim_rows_public(shared: &Shared<'_>, token: &TextToken, rows: &mut Vec<SourceRow>) {
    island_delim_rows(shared, token, rows);
}

/// Coverage rows for a math island's delimiting controls.
fn island_delim_rows(shared: &Shared<'_>, token: &TextToken, rows: &mut Vec<SourceRow>) {
    if let TextToken::Island {
        open,
        close,
        display,
        ..
    } = token
    {
        let (open_entry, close_entry) = if *display {
            ("display-open", "display-close")
        } else {
            ("math-open", "math-close")
        };
        rows.push(structural_row(shared, *open, open_entry));
        rows.push(structural_row(shared, *close, close_entry));
    }
}

fn keyword_rows(shared: &Shared<'_>, keywords: &[Keyword], rows: &mut Vec<SourceRow>) {
    for keyword in keywords {
        rows.push(structural_row(shared, keyword.atom, keyword.entry));
    }
}

/// Elaborate a math island as a term with an optional expected type.
pub fn elab_island(
    shared: &Shared<'_>,
    scopes: &ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    token: &TextToken,
    expected: Option<&Term>,
) -> Result<ElabTerm, Diagnostic> {
    let TextToken::Island {
        inner_start,
        inner_end,
        ..
    } = token
    else {
        return Err(Diagnostic::new(
            code!("LLI9001"),
            "phase elaborate: elab_island received a non-island token",
        ));
    };
    let ast = parse_math(
        shared.path,
        shared.atoms,
        (*inner_start, *inner_end),
        shared.closure,
        shared.visible,
        budget,
    )?;
    let mut elaborator = ExprElab {
        shared,
        scopes,
        alloc,
        budget,
    };
    let mut result = elaborator.elaborate(&ast, expected)?;
    island_delim_rows(shared, token, &mut result.rows);
    Ok(result)
}

/// Elaborate one term phrase (§15.3, §13.4): a mathematical island, or a
/// noun-of / binary-noun-of frame whose IR is the application of the entry
/// to its argument terms. Every candidate entry is tried; semantically
/// identical results collapse and exactly one distinct linked term must
/// remain (§14.4).
pub fn elab_term_phrase(
    shared: &Shared<'_>,
    scopes: &ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    phrase: &TermPhraseAst,
    expected: Option<&Term>,
) -> Result<ElabTerm, Diagnostic> {
    match phrase {
        TermPhraseAst::Island(island) => {
            elab_island(shared, scopes, alloc, budget, island, expected)
        }
        TermPhraseAst::NounOf {
            candidates,
            surface_atoms,
            args,
            keywords,
        } => {
            let mut rows = Vec::new();
            keyword_rows(shared, keywords, &mut rows);
            let mut arg_terms = Vec::new();
            for argument in args {
                let result = elab_term_phrase(shared, scopes, alloc, budget, argument, None)?;
                rows.extend(result.rows.clone());
                arg_terms.push(result);
            }
            let mut survivors: Vec<(String, ElabTerm)> = Vec::new();
            let mut first_failure: Option<Diagnostic> = None;
            for reference in candidates {
                let mut elaborator = ExprElab {
                    shared,
                    scopes,
                    alloc,
                    budget,
                };
                match elaborator.apply_entry_to_terms(reference, *surface_atoms, &arg_terms, expected)
                {
                    Ok(result) => {
                        let key = result.term.eq_key();
                        if !survivors.iter().any(|(existing, _)| *existing == key) {
                            survivors.push((key, result));
                        }
                    }
                    Err(diagnostic) => {
                        if first_failure.is_none() {
                            first_failure = Some(diagnostic);
                        }
                    }
                }
            }
            let a = &shared.atoms[surface_atoms.0];
            match survivors.len() {
                1 => {
                    let (_, mut result) = survivors.into_iter().next().expect("one");
                    rows.append(&mut result.rows);
                    result.rows = rows;
                    Ok(result)
                }
                0 => Err(first_failure.unwrap_or_else(|| {
                    Diagnostic::new(
                        code!("LLT4001"),
                        "no noun-of interpretation satisfies the declared signatures",
                    )
                    .with_span(a.span(shared.path))
                })),
                _ => Err(ambiguity_diagnostic(
                    survivors.iter().map(|(_, result)| &result.term),
                )
                .with_span(a.span(shared.path))),
            }
        }
    }
}

/// The §14.4 ambiguity diagnostic: `LLP2002` presenting only the
/// differentiating qualified candidate IDs (those not shared by every
/// surviving interpretation).
pub(crate) fn ambiguity_diagnostic<'t>(survivors: impl Iterator<Item = &'t Term>) -> Diagnostic {
    let id_sets: Vec<std::collections::BTreeSet<String>> = survivors
        .map(|term| {
            let mut ids = std::collections::BTreeSet::new();
            collect_global_ids(term, &mut ids);
            ids
        })
        .collect();
    let union: std::collections::BTreeSet<String> = id_sets.iter().flatten().cloned().collect();
    let differing: Vec<String> = union
        .iter()
        .filter(|id| !id_sets.iter().all(|set| set.contains(*id)))
        .cloned()
        .collect();
    let candidates = if differing.is_empty() {
        // Every survivor mentions the same entries and differs only in
        // structure (grouping, binding); the full set is the best pointer.
        union.into_iter().collect::<Vec<_>>().join(", ")
    } else {
        differing.join(", ")
    };
    Diagnostic::new(
        code!("LLP2002"),
        format!(
            "{} distinct linked interpretations survive; the differentiating candidates are: {candidates}",
            id_sets.len()
        ),
    )
}

/// Elaborate one text binder (§15.4): the type phrase and the fresh local.
/// Declares the local in the innermost scope frame.
pub fn elab_binder(
    shared: &Shared<'_>,
    scopes: &mut ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    binder: &BinderAst,
) -> Result<(Binder, Vec<SourceRow>), Diagnostic> {
    let mut rows = Vec::new();
    keyword_rows(shared, &binder.keywords, &mut rows);
    let ty = match &binder.type_phrase {
        TypePhraseAst::Noun { candidates, atoms } => {
            let mut survivors: Vec<(String, Term, SourceRow)> = Vec::new();
            for reference in candidates {
                let mut elaborator = ExprElab {
                    shared,
                    scopes,
                    alloc,
                    budget,
                };
                let leaf = crate::grammar::math::MathAst::Leaf {
                    kinds: vec![crate::grammar::math::LeafKind::Form(reference.clone())],
                    atoms: *atoms,
                };
                if let Ok(result) = elaborator.elaborate(&leaf, None) {
                    let key = result.term.eq_key();
                    if !survivors.iter().any(|(existing, ..)| *existing == key) {
                        let row = result.rows[0].clone();
                        survivors.push((key, result.term, row));
                    }
                }
            }
            match survivors.len() {
                1 => {
                    let (_, term, row) = survivors.into_iter().next().expect("one");
                    rows.push(row);
                    term
                }
                0 => {
                    let a = &shared.atoms[atoms.0];
                    return Err(Diagnostic::new(
                        code!("LLT4001"),
                        "no type-noun interpretation survives",
                    )
                    .with_span(a.span(shared.path)));
                }
                _ => {
                    let a = &shared.atoms[atoms.0];
                    return Err(
                        ambiguity_diagnostic(survivors.iter().map(|(_, term, _)| term))
                            .with_span(a.span(shared.path)),
                    );
                }
            }
        }
        TypePhraseAst::Math(island) => {
            let result = elab_island(shared, scopes, alloc, budget, island, None)?;
            match &result.ty {
                Some(Term::Sort(_)) => {}
                _ => {
                    let a = &shared.atoms[island.first_atom()];
                    return Err(Diagnostic::new(
                        code!("LLT4001"),
                        "a binder type phrase must be a sort",
                    )
                    .with_span(a.span(shared.path)));
                }
            }
            rows.extend(result.rows);
            result.term
        }
    };
    let id = alloc.fresh();
    scopes.declare(&binder.spelling, id, Some(ty.clone()));
    island_delim_rows(shared, &binder.island, &mut rows);
    let ident = &shared.atoms[binder.ident_atoms.0];
    rows.push(SourceRow {
        path: shared.path.to_owned(),
        byte_start: ident.byte_start,
        byte_end: shared.atoms[binder.ident_atoms.1 - 1].byte_end,
        class: AtomClass::Word,
        binding: Origin::Local(id.0 as usize),
    });
    Ok((
        Binder {
            id,
            mode: BinderMode::Explicit,
            ty,
            spelling: binder.spelling.clone(),
        },
        rows,
    ))
}

/// Elaborate one proposition parse alternative to a `Prop` term (§15.6).
#[allow(clippy::too_many_lines)]
pub fn elab_proposition(
    shared: &Shared<'_>,
    scopes: &mut ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    ast: &PropAst,
) -> Result<(Term, Vec<SourceRow>), Diagnostic> {
    let core_app = |core: CoreRef, args: Vec<Term>| Term::App {
        function: Box::new(Term::Global(GlobalRef::Core(core), Vec::new())),
        explicit_args: args,
        omitted_implicit_binders: Vec::new(),
    };
    match ast {
        PropAst::Math(island) => {
            let result = elab_island(
                shared,
                scopes,
                alloc,
                budget,
                island,
                Some(&crate::ir::term::prop()),
            )?;
            Ok((result.term, result.rows))
        }
        PropAst::Predicate {
            candidates,
            surface_atoms,
            args,
            keywords,
        } => {
            let mut rows = Vec::new();
            keyword_rows(shared, keywords, &mut rows);
            let mut arg_terms = Vec::new();
            for argument in args {
                let result = elab_term_phrase(shared, scopes, alloc, budget, argument, None)?;
                rows.extend(result.rows.clone());
                arg_terms.push(result);
            }
            // Apply each candidate entry to the argument terms through the
            // shared operator machinery.
            let mut survivors: Vec<(String, Term, Vec<SourceRow>)> = Vec::new();
            let mut first_failure: Option<Diagnostic> = None;
            for reference in candidates {
                let mut elaborator = ExprElab {
                    shared,
                    scopes,
                    alloc,
                    budget,
                };
                match elaborator.apply_entry_to_terms(
                    reference,
                    *surface_atoms,
                    &arg_terms,
                    Some(&crate::ir::term::prop()),
                ) {
                    Ok(result) => {
                        let key = result.term.eq_key();
                        if !survivors.iter().any(|(existing, ..)| *existing == key) {
                            survivors.push((key, result.term, result.rows));
                        }
                    }
                    Err(diagnostic) => {
                        if first_failure.is_none() {
                            first_failure = Some(diagnostic);
                        }
                    }
                }
            }
            match survivors.len() {
                1 => {
                    let (_, term, mut extra) = survivors.into_iter().next().expect("one");
                    rows.append(&mut extra);
                    Ok((term, rows))
                }
                0 => {
                    let a = &shared.atoms[surface_atoms.0];
                    Err(first_failure.unwrap_or_else(|| {
                        Diagnostic::new(
                            code!("LLT4001"),
                            "no predicate interpretation satisfies the declared signatures",
                        )
                        .with_span(a.span(shared.path))
                    }))
                }
                _ => {
                    let a = &shared.atoms[surface_atoms.0];
                    Err(
                        ambiguity_diagnostic(survivors.iter().map(|(_, term, _)| term))
                            .with_span(a.span(shared.path)),
                    )
                }
            }
        }
        PropAst::Not { inner, keywords } => {
            let (inner_term, mut rows) = elab_proposition(shared, scopes, alloc, budget, inner)?;
            keyword_rows(shared, keywords, &mut rows);
            Ok((core_app(CoreRef::Not, vec![inner_term]), rows))
        }
        PropAst::And { items, keywords } | PropAst::Or { items, keywords } => {
            let core = if matches!(ast, PropAst::And { .. }) {
                CoreRef::And
            } else {
                CoreRef::Or
            };
            let mut rows = Vec::new();
            keyword_rows(shared, keywords, &mut rows);
            let mut terms = Vec::new();
            for item in items {
                let (term, item_rows) = elab_proposition(shared, scopes, alloc, budget, item)?;
                rows.extend(item_rows);
                terms.push(term);
            }
            // Left fold: `P and Q and R` is `And (And P Q) R`.
            let mut iterator = terms.into_iter();
            let mut accumulated = iterator.next().ok_or_else(|| {
                Diagnostic::new(code!("LLI9001"), "phase elaborate: empty connective chain")
            })?;
            for next in iterator {
                accumulated = core_app(core, vec![accumulated, next]);
            }
            Ok((accumulated, rows))
        }
        PropAst::Iff {
            left,
            right,
            keywords,
        } => {
            let (left_term, mut rows) = elab_proposition(shared, scopes, alloc, budget, left)?;
            keyword_rows(shared, keywords, &mut rows);
            let (right_term, right_rows) = elab_proposition(shared, scopes, alloc, budget, right)?;
            rows.extend(right_rows);
            Ok((core_app(CoreRef::Iff, vec![left_term, right_term]), rows))
        }
        PropAst::Implies {
            left,
            right,
            keywords,
        }
        | PropAst::Conditional {
            antecedent: left,
            consequent: right,
            keywords,
        } => {
            let (antecedent, mut rows) = elab_proposition(shared, scopes, alloc, budget, left)?;
            keyword_rows(shared, keywords, &mut rows);
            let (consequent, consequent_rows) =
                elab_proposition(shared, scopes, alloc, budget, right)?;
            rows.extend(consequent_rows);
            // Implication is a non-dependent Pi into Prop (§15.6).
            Ok((
                Term::Pi {
                    binders: vec![Binder {
                        id: alloc.fresh(),
                        mode: BinderMode::Explicit,
                        ty: antecedent,
                        spelling: String::new(),
                    }],
                    body: Box::new(consequent),
                },
                rows,
            ))
        }
        PropAst::ForAll {
            binders,
            body,
            keywords,
        } => {
            let mut rows = Vec::new();
            keyword_rows(shared, keywords, &mut rows);
            scopes.push_frame();
            let mut ir_binders = Vec::new();
            for binder in binders {
                let (ir_binder, binder_rows) = elab_binder(shared, scopes, alloc, budget, binder)?;
                rows.extend(binder_rows);
                ir_binders.push(ir_binder);
            }
            let body_result = elab_proposition(shared, scopes, alloc, budget, body);
            scopes.pop_frame();
            let (body_term, body_rows) = body_result?;
            rows.extend(body_rows);
            Ok((
                Term::Pi {
                    binders: ir_binders,
                    body: Box::new(body_term),
                },
                rows,
            ))
        }
        PropAst::Exists {
            binder,
            unique,
            body,
            keywords,
        } => {
            let mut rows = Vec::new();
            keyword_rows(shared, keywords, &mut rows);
            scopes.push_frame();
            let elaborated = elab_binder(shared, scopes, alloc, budget, binder);
            let body_result = match &elaborated {
                Ok(_) => elab_proposition(shared, scopes, alloc, budget, body),
                Err(_) => Err(Diagnostic::new(code!("LLI9001"), "unreachable")),
            };
            scopes.pop_frame();
            let (ir_binder, binder_rows) = elaborated?;
            rows.extend(binder_rows);
            let (body_term, body_rows) = body_result?;
            rows.extend(body_rows);
            let lambda = Term::Lambda {
                binders: vec![ir_binder],
                body: Box::new(body_term),
            };
            let core = if *unique {
                CoreRef::ExistsUnique
            } else {
                CoreRef::Exists
            };
            Ok((
                Term::App {
                    function: Box::new(Term::Global(GlobalRef::Core(core), Vec::new())),
                    explicit_args: vec![lambda],
                    omitted_implicit_binders: vec![ImplicitBinderId(0)],
                },
                rows,
            ))
        }
    }
}

/// Elaborate a full proposition sentence: every complete parse alternative
/// is elaborated, semantically identical results collapse, and exactly one
/// distinct linked interpretation must remain (§14.4, I5).
pub fn elab_proposition_sentence(
    shared: &Shared<'_>,
    scopes: &mut ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    alternatives: &[PropAst],
) -> Result<(Term, Vec<SourceRow>), Diagnostic> {
    let mut survivors: Vec<(String, Term, Vec<SourceRow>)> = Vec::new();
    let mut first_failure: Option<Diagnostic> = None;
    for alternative in alternatives {
        match elab_proposition(shared, scopes, alloc, budget, alternative) {
            Ok((term, rows)) => {
                let key = term.eq_key();
                if !survivors.iter().any(|(existing, ..)| *existing == key) {
                    survivors.push((key, term, rows));
                }
            }
            Err(diagnostic) => {
                if first_failure.is_none() {
                    first_failure = Some(diagnostic);
                }
            }
        }
    }
    match survivors.len() {
        1 => {
            let (_, term, rows) = survivors.into_iter().next().expect("one");
            // Proposition nesting is bounded like term nesting (§25.5).
            budget.depth(term.depth(), "elaborate (proposition nesting)")?;
            Ok((term, rows))
        }
        0 => Err(first_failure.unwrap_or_else(|| {
            Diagnostic::new(code!("LLP2001"), "no proposition interpretation survives")
        })),
        _ => {
            // §14.4: present the minimal differentiating spans and the
            // differentiating qualified candidate IDs.
            let mut diagnostic = ambiguity_diagnostic(survivors.iter().map(|(_, term, _)| term));
            if let Some(span) = differentiating_span(shared, &survivors) {
                diagnostic = diagnostic.with_span(span);
            }
            Err(diagnostic)
        }
    }
}

/// The minimal differentiating span among surviving alternatives (§14.4):
/// the earliest coverage row that not every survivor shares; when the
/// survivors cover identical bytes with identical bindings, the span of the
/// whole first alternative.
fn differentiating_span(
    shared: &Shared<'_>,
    survivors: &[(String, Term, Vec<SourceRow>)],
) -> Option<crate::diagnostic::Span> {
    let row_span = |row: &SourceRow| {
        let first = shared
            .atoms
            .iter()
            .find(|atom| atom.byte_start == row.byte_start)?;
        let last = shared
            .atoms
            .iter()
            .rev()
            .find(|atom| atom.byte_end == row.byte_end)?;
        Some(crate::diagnostic::Span {
            path: shared.path.to_owned(),
            byte_start: row.byte_start,
            byte_end: row.byte_end,
            line_start: first.line_start,
            column_start: first.column_start,
            line_end: last.line_end,
            column_end: last.column_end,
        })
    };
    let mut candidates: Vec<&SourceRow> = survivors
        .iter()
        .flat_map(|(_, _, rows)| rows.iter())
        .filter(|row| !survivors.iter().all(|(_, _, rows)| rows.contains(row)))
        .collect();
    candidates.sort_by_key(|row| (row.byte_start, row.byte_end));
    if let Some(row) = candidates.first() {
        return row_span(row);
    }
    let (_, _, rows) = survivors.first()?;
    let start = rows.iter().map(|row| row.byte_start).min()?;
    let end = rows.iter().map(|row| row.byte_end).max()?;
    let first = shared.atoms.iter().find(|atom| atom.byte_start == start)?;
    let last = shared.atoms.iter().rev().find(|atom| atom.byte_end == end)?;
    Some(crate::diagnostic::Span {
        path: shared.path.to_owned(),
        byte_start: start,
        byte_end: end,
        line_start: first.line_start,
        column_start: first.column_start,
        line_end: last.line_end,
        column_end: last.column_end,
    })
}

/// Every qualified global reference inside a term (§14.4 candidate IDs).
pub(crate) fn collect_global_ids(term: &Term, out: &mut std::collections::BTreeSet<String>) {
    match term {
        Term::Global(global, _) => {
            let id = match global {
                crate::ir::term::GlobalRef::Core(core) => {
                    format!("lexlean.core::{}", core.as_str())
                }
                crate::ir::term::GlobalRef::External(external) => external.entry.clone(),
                crate::ir::term::GlobalRef::Document(document) => {
                    format!("{}::{}", document.module, document.component)
                }
                crate::ir::term::GlobalRef::DefinedLexicon(defined) => defined.entry.clone(),
            };
            out.insert(id);
        }
        Term::App {
            function,
            explicit_args,
            ..
        } => {
            collect_global_ids(function, out);
            for argument in explicit_args {
                collect_global_ids(argument, out);
            }
        }
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            for binder in binders {
                collect_global_ids(&binder.ty, out);
            }
            collect_global_ids(body, out);
        }
        Term::Let {
            binder,
            value,
            body,
        } => {
            collect_global_ids(&binder.ty, out);
            collect_global_ids(value, out);
            collect_global_ids(body, out);
        }
        Term::NatLiteral { expected_type, .. } => collect_global_ids(expected_type, out),
        Term::Sort(_) | Term::Local(_) => {}
    }
}
