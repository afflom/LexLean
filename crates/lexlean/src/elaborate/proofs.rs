//! Structured proof elaboration (SPEC.md §16): conservative goal tracking
//! over the closed proof IR. Lean elaboration is final (§16.1); LexLean
//! rejects only what is statically certain to be malformed and never
//! accepts a form outside the registered set.

use std::collections::{BTreeMap, BTreeSet};

use crate::code;
use crate::diagnostic::{Diagnostic, Span};
use crate::elaborate::delta::{beta, certainly_distinct, is_closed_shape};
use crate::elaborate::expressions::{
    entry_signature_term, flatten_pi, instantiate_telescope, subst, unify_closed, ElabTerm,
    ExprElab, Instantiated,
};
use crate::elaborate::resolve::{LocalAlloc, ScopeStack};
use crate::elaborate::{elab_island, elab_proposition_sentence, Shared};
use crate::grammar::chart::{text_tokens, Budget, TextToken};
use crate::grammar::math::parse_math;
use crate::grammar::proof::{parse_proof_sentence, ProofSentence, SentenceAstKind};
use crate::grammar::proposition::TextParser;
use crate::grammar::structural::{
    AtomRange, BraceArg, CaseAst, ProofEnvAst, ProofItemAst, SentenceAst,
};
use crate::ir::proof::{CalculationStep, CaseProof, Proof, RewriteRule, RewriteTarget};
use crate::ir::term::{Binder, CoreRef, GlobalRef, ImplicitBinderId, LocalId, Term};
use crate::lexicon::entry::{Category, Eliminator};
use crate::lexicon::lse::{BinderMode, QualifiedId};
use crate::source::atom::AtomClass;
use crate::source::coverage::{Origin, SourceRow};
use crate::source::scan::compose_identifier;

/// The conservative goal state (§16.1).
#[derive(Debug, Clone)]
pub enum Goal {
    /// The goal term is statically known.
    Known(Term),
    /// The goal exists but its shape is not statically computable (after a
    /// step whose result LexLean cannot compute, or inside a branch whose
    /// specialization is unknown). Steps are accepted; Lean is final.
    Unknown,
    /// A rewrite or `simp only` at the goal may have closed it (pinned
    /// Lean's `rw` closes goals that become `rfl`, and `simp only` closes
    /// goals it reduces to `True`): the proof may end here, or continue
    /// against an unknown goal. Lean is final.
    MaybeClosed,
}

impl Goal {
    fn known(&self) -> Option<&Term> {
        match self {
            Self::Known(term) => Some(term),
            Self::Unknown | Self::MaybeClosed => None,
        }
    }

    /// The goal a further step sees: a possibly closed goal is unknown.
    fn for_step(&self) -> Self {
        match self {
            Self::MaybeClosed => Self::Unknown,
            other => other.clone(),
        }
    }
}

/// The residual premises of applying a proof term to the current goal
/// (§16.2, §16.6).
enum Residuals {
    /// The signature and goal suffice: exactly these premises remain, in
    /// signature order.
    Known(Vec<Goal>),
    /// The signature or the goal is unknown, or the conclusion does not
    /// conservatively unify with the goal; Lean is final.
    Unknown,
}

/// The proof elaborator for one declaration.
pub struct ProofElab<'a, 'b> {
    /// The shared module context.
    pub shared: &'b Shared<'a>,
    /// The scopes; the statement binders are already declared.
    pub scopes: &'b mut ScopeStack,
    /// The allocator.
    pub alloc: &'b mut LocalAlloc,
    /// The budget.
    pub budget: &'b mut Budget,
    /// Collected coverage rows.
    pub rows: Vec<SourceRow>,
    /// Display spellings of proof-introduced locals, for canonical
    /// formatting; identity stays the `LocalId` (I9).
    pub spellings: BTreeMap<LocalId, String>,
    /// Spellings of the statement's leading universal binders that the
    /// linker lifted to declaration parameters (§18.5): they are already in
    /// scope, so `Assume` of one is diagnosed by name.
    pub lifted: BTreeSet<String>,
    /// The proof step currently being elaborated, so a resource failure
    /// raised while reading a goal through its definitions still points at
    /// source (§20.1). The declaration's own span until the first step.
    pub span: Span,
}

fn fail(code: crate::diagnostic::DiagnosticCode, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code, message)
}

/// The head global of a term: the applied function of an application, or
/// the term itself.
fn head_global(term: &Term) -> Option<&GlobalRef> {
    match term {
        Term::Global(global, _) => Some(global),
        Term::App { function, .. } => match &**function {
            Term::Global(global, _) => Some(global),
            _ => None,
        },
        _ => None,
    }
}

/// Is a statically known goal headed by a core connective? Such goals have
/// an exact shape LexLean checks; every other head (a document or external
/// predicate that may unfold) defers to Lean (§16.1).
fn core_head(term: &Term) -> Option<CoreRef> {
    match head_global(term) {
        Some(GlobalRef::Core(core)) => Some(*core),
        _ => None,
    }
}

impl<'a, 'b> ProofElab<'a, 'b> {
    /// Read a term through every definition (§17.7, §13.6): the one delta
    /// unfolder over this module's declaration table and closure, bounded
    /// by the configured nesting and IR-size limits. A limit failure names
    /// the proof step being elaborated.
    fn unfold(&mut self, term: &Term) -> Result<Term, Diagnostic> {
        let span = self.span.clone();
        crate::elaborate::delta::unfold(term, self.shared, self.alloc, self.budget)
            .map_err(|diagnostic| diagnostic.with_span(span))
    }

    fn span_of(&self, range: AtomRange) -> Span {
        let first = &self.shared.atoms[range.0];
        let last = &self.shared.atoms[range.1.saturating_sub(1).max(range.0)];
        Span {
            path: self.shared.path.to_owned(),
            byte_start: first.byte_start,
            byte_end: last.byte_end,
            line_start: first.line_start,
            column_start: first.column_start,
            line_end: last.line_end,
            column_end: last.column_end,
        }
    }

    fn item_span(&self, item: &ProofItemAst) -> Span {
        self.span_of(item.span_atoms())
    }

    fn structural_row(&mut self, atom: usize, entry: &str) {
        let a = &self.shared.atoms[atom];
        self.rows.push(SourceRow {
            path: self.shared.path.to_owned(),
            byte_start: a.byte_start,
            byte_end: a.byte_end,
            class: a.class,
            binding: Origin::Structural {
                package: "lexlean.core".to_owned(),
                entry: entry.to_owned(),
            },
        });
    }

    /// A proof term never contains a hole (§16.12): a standalone `_` or a
    /// `?_` in a proof-term island is a forbidden proof form, diagnosed by
    /// name before lexical resolution reports an unknown atom.
    fn reject_holes(&self, range: AtomRange) -> Result<(), Diagnostic> {
        for index in range.0..range.1 {
            let atom = &self.shared.atoms[index];
            if atom.class != AtomClass::AsciiSymbol {
                continue;
            }
            let adjacent_ident = |other: Option<&crate::source::atom::Atom>, before: bool| {
                other.is_some_and(|other| {
                    matches!(other.class, AtomClass::Word | AtomClass::Numeral)
                        && if before {
                            other.byte_end == atom.byte_start
                        } else {
                            other.byte_start == atom.byte_end
                        }
                })
            };
            let previous = index.checked_sub(1).and_then(|i| self.shared.atoms.get(i));
            let next = self
                .shared
                .atoms
                .get(index + 1)
                .filter(|_| index + 1 < range.1);
            let hole = match atom.text.as_str() {
                "_" => !adjacent_ident(previous, true) && !adjacent_ident(next, false),
                "?" => next.is_some_and(|n| n.text == "_" && n.byte_start == atom.byte_end),
                _ => false,
            };
            if hole {
                let spelling = if atom.text == "?" { "?_" } else { "_" };
                return Err(fail(
                    code!("LLF5005"),
                    format!("`{spelling}` is a forbidden proof form (§16.12): a proof term contains no hole"),
                )
                .with_span(atom.span(self.shared.path)));
            }
        }
        Ok(())
    }

    fn term_island(
        &mut self,
        token: &TextToken,
        expected: Option<&Term>,
    ) -> Result<ElabTerm, Diagnostic> {
        if let TextToken::Island {
            inner_start,
            inner_end,
            ..
        } = token
        {
            self.reject_holes((*inner_start, *inner_end))?;
        }
        let result = elab_island(
            self.shared,
            self.scopes,
            self.alloc,
            self.budget,
            token,
            expected,
        )?;
        self.rows.extend(result.rows.clone());
        Ok(result)
    }

    /// Elaborate a proof-term island against a known goal, conservatively:
    /// first with the goal as the expected type (unification sees through
    /// definitions, §17.7), then without an expected type when the term has
    /// one interpretation on its own — LexLean's unifier does not claim
    /// Lean's definitional equality (§17.6), so a term that elaborates
    /// uniquely is handed to Lean, which is final (§16.1), unless its type
    /// and the goal are of shapes no unfolding can reconcile. A term with
    /// no interpretation at all keeps the first, expected-type-directed
    /// diagnostic.
    fn term_against_goal(
        &mut self,
        token: &TextToken,
        goal: Option<&Term>,
    ) -> Result<ElabTerm, Diagnostic> {
        let Some(goal_term) = goal else {
            return self.term_island(token, None);
        };
        let first = match self.term_island(token, Some(goal_term)) {
            Ok(term) => return Ok(term),
            Err(diagnostic) => diagnostic,
        };
        // Without an expected type, the term must still have exactly one
        // interpretation, and the mismatch must be one LexLean cannot judge
        // (§17.6): a numeral against a constructor, two entries for one Lean
        // constant, an external definition, ... are all Lean's to decide. A
        // mismatch is certain only between shapes no definitional unfolding
        // can reconcile — two different core connectives, a function type
        // against a core proposition other than a negation, a sort against
        // either — and stays rejected.
        let goal_unfolded = self.unfold(goal_term)?;
        match self.term_island(token, None) {
            Ok(term) => {
                let certain = match term.ty.as_ref() {
                    Some(ty) => {
                        let ty_unfolded = self.unfold(ty)?;
                        certainly_distinct(&goal_unfolded, &ty_unfolded)
                    }
                    None => false,
                };
                if certain {
                    Err(first)
                } else {
                    Ok(term)
                }
            }
            Err(_) => Err(first),
        }
    }

    /// A brace argument that holds one mathematical term (§16.4–§16.10).
    fn term_brace(&mut self, arg: &BraceArg) -> Result<ElabTerm, Diagnostic> {
        self.term_brace_expected(arg, None)
    }

    fn term_brace_expected(
        &mut self,
        arg: &BraceArg,
        expected: Option<&Term>,
    ) -> Result<ElabTerm, Diagnostic> {
        self.reject_holes(arg.range)?;
        let covers = parse_math(
            self.shared.path,
            self.shared.atoms,
            arg.range,
            self.shared.closure,
            self.shared.visible,
            self.budget,
        )?;
        let mut elaborator = ExprElab::new(self.shared, self.scopes, self.alloc, self.budget);
        let result = elaborator.elaborate_covers(&covers, expected)?;
        self.rows.extend(result.rows.clone());
        Ok(result)
    }

    /// Elaborate one complete proof environment against a goal. The proof
    /// must close every goal (§16.1, LLF5004) and rejects steps after
    /// closure and empty proofs (§16.12).
    pub fn elab_env(&mut self, env: &ProofEnvAst, goal: Goal) -> Result<Proof, Diagnostic> {
        if env.items.is_empty() {
            return Err(fail(code!("LLF5005"), "an empty proof is rejected")
                .with_span(self.span_of((env.begin, env.begin + 1))));
        }
        self.scopes.push_frame();
        let result = self.elab_items(&env.items, goal, env.begin);
        self.scopes.pop_frame();
        let steps = result?;
        Ok(if steps.len() == 1 {
            steps.into_iter().next().expect("one step")
        } else {
            Proof::Sequence(steps)
        })
    }

    #[allow(clippy::too_many_lines)]
    fn elab_items(
        &mut self,
        items: &[ProofItemAst],
        mut goal: Goal,
        env_begin: usize,
    ) -> Result<Vec<Proof>, Diagnostic> {
        let mut steps: Vec<Proof> = Vec::new();
        let mut closed = false;
        for item in items {
            if closed {
                return Err(fail(
                    code!("LLF5002"),
                    "a proof step after the current branch has closed",
                )
                .with_span(self.item_span(item)));
            }
            self.span = self.item_span(item);
            let step_goal = match goal.for_step() {
                Goal::Known(term) => Goal::Known(self.unfold(&term)?),
                other => other,
            };
            match item {
                ProofItemAst::Sentence(sentence) => {
                    let (step, next_goal, now_closed) =
                        self.simple_sentence(sentence, step_goal)?;
                    steps.push(step);
                    goal = next_goal;
                    closed = now_closed;
                }
                ProofItemAst::Have {
                    name,
                    proposition,
                    proof,
                    ..
                } => {
                    // The hypothesis name is an LSE identifier and never the
                    // reserved target word `goal` (§16.3, §16.4).
                    if !crate::lexicon::lse::is_lse_identifier(&name.text) || name.text == "goal" {
                        return Err(fail(
                            code!("LLF5002"),
                            format!(
                                "`{}` is not a valid hypothesis name: an ASCII identifier other than `goal` is required",
                                name.text
                            ),
                        )
                        .with_span(self.span_of(name.range)));
                    }
                    if !self.scopes.is_fresh(&name.text) {
                        return Err(fail(
                            code!("LLF5002"),
                            format!("`{}` is not fresh in the current proof scope", name.text),
                        )
                        .with_span(self.span_of(name.range)));
                    }
                    let prop_term = self.proposition_sentence(proposition)?;
                    // The nested proof cannot see the hypothesis (§16.3).
                    let nested = self.elab_env(proof, Goal::Known(prop_term.clone()))?;
                    let local = self.alloc.fresh();
                    self.scopes
                        .declare(&name.text, local, Some(prop_term.clone()));
                    self.spellings.insert(local, name.text.clone());
                    steps.push(Proof::Have {
                        local,
                        proposition: prop_term,
                        proof: Box::new(nested),
                    });
                    goal = step_goal;
                }
                ProofItemAst::Rewrite { target, rules, .. } => {
                    let rewrite_target = self.rewrite_target(target)?;
                    let mut ir_rules = Vec::new();
                    for (reverse, rule) in rules {
                        let term = self.term_brace(rule)?;
                        self.check_equation_shaped(&term, rule)?;
                        ir_rules.push(RewriteRule {
                            reverse: *reverse,
                            term: term.term,
                        });
                    }
                    goal = match &rewrite_target {
                        RewriteTarget::Goal => Goal::MaybeClosed,
                        RewriteTarget::Hypothesis(id) => {
                            self.scopes.forget_type(*id);
                            step_goal
                        }
                    };
                    steps.push(Proof::Rewrite {
                        target: rewrite_target,
                        rules: ir_rules,
                    });
                }
                ProofItemAst::Simplify { target, rules, .. } => {
                    let rewrite_target = self.rewrite_target(target)?;
                    let mut ir_rules = Vec::new();
                    for rule in rules {
                        let term = self.term_brace(rule)?;
                        self.check_simp_rule(&term, rule)?;
                        ir_rules.push(term.term);
                    }
                    goal = match &rewrite_target {
                        RewriteTarget::Goal => Goal::MaybeClosed,
                        RewriteTarget::Hypothesis(id) => {
                            self.scopes.forget_type(*id);
                            step_goal
                        }
                    };
                    steps.push(Proof::SimplifyOnly {
                        target: rewrite_target,
                        rules: ir_rules,
                    });
                }
                ProofItemAst::Apply {
                    function, premises, ..
                } => {
                    let function_term = self.term_brace(function)?;
                    let residuals = self.residual_premises(&function_term, &step_goal)?;
                    // Premise labels are consecutive decimal integers from 1
                    // and every residual premise occurs exactly once (§16.6).
                    for (index, (label, body)) in premises.iter().enumerate() {
                        if *label != (index as u64) + 1 {
                            return Err(fail(
                                code!("LLF5003"),
                                format!(
                                    "premise labels are consecutive decimal integers beginning with 1, found {label} at position {}",
                                    index + 1
                                ),
                            )
                            .with_span(self.span_of((body.begin, body.begin + 1))));
                        }
                    }
                    if let Residuals::Known(expected) = &residuals {
                        if expected.len() != premises.len() {
                            return Err(fail(
                                code!("LLF5003"),
                                format!(
                                    "the applied signature yields {} residual premises, found {}",
                                    expected.len(),
                                    premises.len()
                                ),
                            )
                            .with_span(self.item_span(item)));
                        }
                    }
                    let mut premise_proofs = Vec::new();
                    for (index, (_, body)) in premises.iter().enumerate() {
                        let premise_goal = match &residuals {
                            Residuals::Known(expected) => {
                                expected.get(index).cloned().unwrap_or(Goal::Unknown)
                            }
                            Residuals::Unknown => Goal::Unknown,
                        };
                        premise_proofs.push(self.elab_env(body, premise_goal)?);
                    }
                    steps.push(Proof::Apply {
                        function: function_term.term,
                        premises: premise_proofs,
                    });
                    closed = true;
                }
                ProofItemAst::Constructor { branches, .. } => {
                    for (index, (label, body)) in branches.iter().enumerate() {
                        if *label != (index as u64) + 1 {
                            return Err(fail(
                                code!("LLF5003"),
                                format!(
                                    "branch labels are consecutive decimal integers beginning with 1, found {label} at position {}",
                                    index + 1
                                ),
                            )
                            .with_span(self.span_of((body.begin, body.begin + 1))));
                        }
                    }
                    let branch_goals: Option<Vec<Goal>> = match step_goal.known() {
                        Some(term) => match self.constructor_fields(term) {
                            Some(fields) => Some(fields),
                            None if is_closed_shape(term) => {
                                // §16.7: a statically known goal headed by a
                                // core connective must be a constructor
                                // target with proof fields.
                                return Err(fail(
                                    code!("LLF5002"),
                                    "the goal is not a constructor target: constructor splits a conjunction, a biconditional, or a glossary-declared structure",
                                )
                                .with_span(self.item_span(item)));
                            }
                            // An unknown-headed goal may unfold to a
                            // structure; Lean is final.
                            None => None,
                        },
                        None => None,
                    };
                    if let Some(expected) = &branch_goals {
                        if expected.len() != branches.len() {
                            return Err(fail(
                                code!("LLF5003"),
                                format!(
                                    "the target constructor has {} explicit proof fields, found {} branches",
                                    expected.len(),
                                    branches.len()
                                ),
                            )
                            .with_span(self.item_span(item)));
                        }
                    }
                    let mut branch_proofs = Vec::new();
                    for (index, (_, body)) in branches.iter().enumerate() {
                        let branch_goal = branch_goals
                            .as_ref()
                            .and_then(|expected| expected.get(index).cloned())
                            .unwrap_or(Goal::Unknown);
                        branch_proofs.push(self.elab_env(body, branch_goal)?);
                    }
                    steps.push(Proof::Constructor(branch_proofs));
                    closed = true;
                }
                ProofItemAst::CasesLike {
                    induction,
                    scrutinee,
                    cases,
                    begin,
                } => {
                    let step = self.cases_like(*induction, scrutinee, cases, &step_goal, *begin)?;
                    steps.push(step);
                    closed = true;
                }
                ProofItemAst::Calculate {
                    start, steps: calc, ..
                } => {
                    let step = self.calculate(start, calc, &step_goal)?;
                    steps.push(step);
                    closed = true;
                }
            }
        }
        if !closed && !matches!(goal, Goal::MaybeClosed) {
            let span = match items.last() {
                Some(last) => self.item_span(last),
                None => self.span_of((env_begin, env_begin + 1)),
            };
            return Err(fail(
                code!("LLF5004"),
                "the proof does not close all goals: the last step leaves a goal open",
            )
            .with_span(span));
        }
        Ok(steps)
    }

    fn proposition_sentence(&mut self, sentence: &SentenceAst) -> Result<Term, Diagnostic> {
        let tokens = text_tokens(
            self.shared.path,
            self.shared.atoms,
            sentence.range.0,
            sentence.range.1,
        )?;
        let parser = TextParser {
            path: self.shared.path,
            atoms: self.shared.atoms,
            tokens: &tokens,
            closure: self.shared.closure,
            visible: self.shared.visible,
            sentence_initial: true,
        };
        let alternatives = parser.proposition_sentence(self.budget)?;
        let (term, rows) = elab_proposition_sentence(
            self.shared,
            self.scopes,
            self.alloc,
            self.budget,
            &alternatives,
        )?;
        self.rows.extend(rows);
        self.structural_row(sentence.period, "period");
        Ok(term)
    }

    /// Is a known local type a data type rather than a proposition? A sort,
    /// or a type headed by a type-noun entry, types data binders; a rewrite
    /// or simplify hypothesis target must be a proposition (§16.4).
    fn is_data_type(&self, ty: &Term) -> bool {
        if matches!(ty, Term::Sort(_)) {
            return true;
        }
        let entry_id = match head_global(ty) {
            Some(GlobalRef::External(external)) => QualifiedId::parse(&external.entry).ok(),
            Some(GlobalRef::DefinedLexicon(defined)) => QualifiedId::parse(&defined.entry).ok(),
            _ => None,
        };
        entry_id
            .and_then(|id| self.shared.closure.entry(&id))
            .is_some_and(|entry| entry.category == Category::TypeNoun)
    }

    fn rewrite_target(&mut self, target: &BraceArg) -> Result<RewriteTarget, Diagnostic> {
        if target.text == "goal" {
            return Ok(RewriteTarget::Goal);
        }
        match self.scopes.lookup(&target.text) {
            Some(entry) => {
                let entry = entry.clone();
                let data = match &entry.ty {
                    Some(ty) => {
                        let unfolded = self.unfold(ty)?;
                        self.is_data_type(&unfolded)
                    }
                    None => false,
                };
                if data {
                    return Err(fail(
                        code!("LLF5002"),
                        format!(
                            "`{}` is a data binder, not a hypothesis; a rewrite or simplify target is `goal` or a proposition-typed proof local",
                            target.text
                        ),
                    )
                    .with_span(self.span_of(target.range)));
                }
                Ok(RewriteTarget::Hypothesis(entry.id))
            }
            None => Err(fail(
                code!("LLF5002"),
                format!(
                    "the target is exactly `goal` or an in-scope proof-local spelling, found `{}`",
                    target.text
                ),
            )
            .with_span(self.span_of(target.range))),
        }
    }

    fn check_equation_shaped(&mut self, term: &ElabTerm, arg: &BraceArg) -> Result<(), Diagnostic> {
        // A rule term must prove an equality or equivalence when its type
        // is statically known (§16.4), read through its definitions.
        // Unknown types defer to Lean.
        let Some(ty) = &term.ty else {
            return Ok(());
        };
        let ty = self.unfold(ty)?;
        let (_, conclusion) = flatten_pi(&ty);
        if matches!(core_head(&conclusion), Some(CoreRef::Eq | CoreRef::Iff)) {
            return Ok(());
        }
        // A conclusion headed by an external predicate may still unfold to
        // an equation in Lean; only a closed shape or a data type is
        // certainly not one.
        if !is_closed_shape(&conclusion) && !self.is_data_type(&conclusion) {
            return Ok(());
        }
        Err(fail(
            code!("LLF5002"),
            "a rewrite rule proves an equality or equivalence",
        )
        .with_span(self.span_of(arg.range)))
    }

    fn check_simp_rule(&mut self, term: &ElabTerm, arg: &BraceArg) -> Result<(), Diagnostic> {
        // A simp rule is a proof of a proposition (an equation, an
        // equivalence, or any proposition read as `= True`); a data term is
        // certainly not one (§16.5).
        let Some(ty) = &term.ty else {
            return Ok(());
        };
        let ty = self.unfold(ty)?;
        let (_, conclusion) = flatten_pi(&ty);
        if self.is_data_type(&conclusion) {
            return Err(fail(
                code!("LLF5002"),
                "a simplify rule is a proof term, not a data term",
            )
            .with_span(self.span_of(arg.range)));
        }
        Ok(())
    }

    /// The residual explicit premises of applying a proof term to the
    /// current goal (§16.2, §16.6): the signature telescope is flattened,
    /// every binder becomes a metavariable, the conclusion is unified with
    /// the goal, and the explicit binders unification left unsolved are the
    /// residual premises, in signature order.
    fn residual_premises(
        &mut self,
        function: &ElabTerm,
        goal: &Goal,
    ) -> Result<Residuals, Diagnostic> {
        let Some(ty) = function.ty.as_ref() else {
            return Ok(Residuals::Unknown);
        };
        // A conclusion headed by a definition (document or defined lexicon
        // value) is read through its definition, as Lean's `apply` does.
        let ty = &self.unfold(ty)?;
        let (binders, conclusion) = flatten_pi(ty);
        if binders.is_empty() {
            // `Not P` is `P → False`: applying a negation leaves exactly the
            // premise `P` (§16.2).
            if let (Some(CoreRef::Not), Term::App { explicit_args, .. }) =
                (core_head(&conclusion), &conclusion)
            {
                if let [premise] = explicit_args.as_slice() {
                    return Ok(Residuals::Known(vec![Goal::Known(premise.clone())]));
                }
            }
            // A closed shape has no premises; an open head (an external
            // predicate such as `Ne`, a local) may still reduce to a
            // function type in Lean, which is final.
            return Ok(if is_closed_shape(&conclusion) {
                Residuals::Known(Vec::new())
            } else {
                Residuals::Unknown
            });
        }
        let Some(goal_term) = goal.known() else {
            return Ok(Residuals::Unknown);
        };
        let Some(instantiated) = instantiate_telescope(ty, Some(goal_term), self.alloc) else {
            return Ok(Residuals::Unknown);
        };
        let mut residuals = Vec::new();
        for (index, (binder, _)) in instantiated.binders.iter().enumerate() {
            if binder.mode != BinderMode::Explicit || !instantiated.binder_unsolved(index) {
                continue;
            }
            residuals.push(match instantiated.binder_type(index) {
                Some(premise) => Goal::Known(premise),
                None => Goal::Unknown,
            });
        }
        Ok(Residuals::Known(residuals))
    }

    /// The glossary eliminator descriptor of a type, found through the head
    /// global of the (zonked) type: an external or defined type-noun, or a
    /// core connective whose core entry carries a descriptor (§16.8, §16.11).
    fn descriptor_for_type(&self, ty: &Term) -> Option<(QualifiedId, Eliminator)> {
        let entry_id = match head_global(ty)? {
            GlobalRef::External(external) => QualifiedId::parse(&external.entry).ok()?,
            GlobalRef::DefinedLexicon(defined) => QualifiedId::parse(&defined.entry).ok()?,
            // A core-headed type finds the core entry that carries its
            // constructor (for example `logic.exists` → `exists-op`); the
            // descriptor, when any, lives on that entry (§16.11).
            GlobalRef::Core(core) => self
                .shared
                .closure
                .core_entry_for_constructor(core.constructor_name())?,
            GlobalRef::Document(_) => return None,
        };
        let entry = self.shared.closure.entry(&entry_id)?;
        Some((entry_id, entry.eliminator.clone()?))
    }

    /// Instantiate a constructor entry's signature against the scrutinee
    /// type: the explicit binders are the constructor's fields, typed by the
    /// type's arguments (§16.8). `None` when the entry, its signature, or
    /// the unification is unavailable; the fields are then untyped.
    fn constructor_instance(
        &mut self,
        constructor: &QualifiedId,
        target: &Term,
    ) -> Option<(GlobalRef, Instantiated)> {
        let (global, signature) =
            entry_signature_term(self.shared, self.alloc, constructor).ok()?;
        let instantiated = instantiate_telescope(&signature, Some(target), self.alloc)?;
        Some((global, instantiated))
    }

    /// The branch goals of `constructor` on a known goal (§16.7): the two
    /// conjuncts, the two implications of a biconditional, or the explicit
    /// proof fields of a glossary-declared structure with exactly one
    /// constructor whose descriptor the goal's head entry carries.
    fn constructor_fields(&mut self, goal: &Term) -> Option<Vec<Goal>> {
        if let Term::App {
            function,
            explicit_args,
            ..
        } = goal
        {
            if let Term::Global(GlobalRef::Core(core), _) = &**function {
                match core {
                    CoreRef::And => {
                        if explicit_args.len() == 2 {
                            return Some(explicit_args.iter().cloned().map(Goal::Known).collect());
                        }
                    }
                    CoreRef::Iff => {
                        if let [left, right] = explicit_args.as_slice() {
                            let arrow = |from: &Term, to: &Term, alloc: &mut LocalAlloc| Term::Pi {
                                binders: vec![Binder {
                                    id: alloc.fresh(),
                                    mode: BinderMode::Explicit,
                                    ty: from.clone(),
                                    spelling: String::new(),
                                }],
                                body: Box::new(to.clone()),
                            };
                            let forward = arrow(left, right, self.alloc);
                            let backward = arrow(right, left, self.alloc);
                            return Some(vec![Goal::Known(forward), Goal::Known(backward)]);
                        }
                    }
                    _ => {}
                }
            }
        }
        // A glossary-declared structure: exactly one constructor in the
        // head entry's descriptor; its explicit fields are the branch goals.
        let (_, eliminator) = self.descriptor_for_type(goal)?;
        let [constructor] = eliminator.constructors.as_slice() else {
            return None;
        };
        let (_, instantiated) = self.constructor_instance(&constructor.entry, goal)?;
        let mut fields = Vec::new();
        for (index, (binder, _)) in instantiated.binders.iter().enumerate() {
            if binder.mode != BinderMode::Explicit {
                continue;
            }
            fields.push(match instantiated.binder_type(index) {
                Some(ty) => Goal::Known(ty),
                None => Goal::Unknown,
            });
        }
        Some(fields)
    }

    fn assume_locals(
        &mut self,
        sentence: &SentenceAst,
        islands: &[TextToken],
    ) -> Result<Vec<(String, usize, usize, TextToken)>, Diagnostic> {
        let mut out: Vec<(String, usize, usize, TextToken)> = Vec::new();
        for island in islands {
            let TextToken::Island {
                inner_start,
                inner_end,
                ..
            } = island
            else {
                continue;
            };
            let mut index = *inner_start;
            while index < *inner_end && self.shared.atoms[index].class == AtomClass::Whitespace {
                index += 1;
            }
            let Some((spelling, ident_end)) = compose_identifier(self.shared.atoms, index) else {
                return Err(fail(
                    code!("LLF5002"),
                    "Assume introduces fresh local identifiers",
                )
                .with_span(self.span_of(sentence.range)));
            };
            let mut rest = ident_end;
            while rest < *inner_end && self.shared.atoms[rest].class == AtomClass::Whitespace {
                rest += 1;
            }
            if rest != *inner_end {
                return Err(fail(
                    code!("LLF5002"),
                    "Assume introduces fresh local identifiers, one per island",
                )
                .with_span(self.span_of((index, *inner_end))));
            }
            if !self.scopes.is_fresh(&spelling) {
                let message = if self.lifted.contains(&spelling) {
                    format!(
                        "`{spelling}` is a leading universal binder of the statement and is already a declaration parameter in scope throughout the proof (§15.8); Assume introduces only the goal's remaining binders"
                    )
                } else {
                    format!("`{spelling}` is not fresh in the current proof scope")
                };
                return Err(
                    fail(code!("LLF5002"), message).with_span(self.span_of((index, ident_end)))
                );
            }
            if out.iter().any(|(existing, ..)| *existing == spelling) {
                return Err(fail(
                    code!("LLF5002"),
                    format!("`{spelling}` is introduced twice in one Assume"),
                )
                .with_span(self.span_of((index, ident_end))));
            }
            out.push((spelling, index, ident_end, island.clone()));
        }
        Ok(out)
    }

    fn declare_assumed(
        &mut self,
        spelling: &str,
        id: LocalId,
        ty: Option<Term>,
        ident: (usize, usize),
        island: &TextToken,
    ) {
        self.scopes.declare(spelling, id, ty);
        self.spellings.insert(id, spelling.to_owned());
        let mut rows = Vec::new();
        crate::elaborate::island_delim_rows_public(self.shared, island, &mut rows);
        self.rows.extend(rows);
        let ident_first = &self.shared.atoms[ident.0];
        self.rows.push(SourceRow {
            path: self.shared.path.to_owned(),
            byte_start: ident_first.byte_start,
            byte_end: self.shared.atoms[ident.1 - 1].byte_end,
            class: AtomClass::Word,
            binding: Origin::Local(id.0 as usize),
        });
    }

    #[allow(clippy::too_many_lines)]
    fn simple_sentence(
        &mut self,
        sentence: &SentenceAst,
        goal: Goal,
    ) -> Result<(Proof, Goal, bool), Diagnostic> {
        let tokens = text_tokens(
            self.shared.path,
            self.shared.atoms,
            sentence.range.0,
            sentence.range.1,
        )?;
        let parser = TextParser {
            path: self.shared.path,
            atoms: self.shared.atoms,
            tokens: &tokens,
            closure: self.shared.closure,
            visible: self.shared.visible,
            sentence_initial: true,
        };
        let ProofSentence { kind, keywords } = parse_proof_sentence(&parser)?;
        for keyword in &keywords {
            self.structural_row(keyword.atom, keyword.entry);
        }
        self.structural_row(sentence.period, "period");
        let sentence_span = self.span_of(sentence.range);
        // A goal headed by a definition is seen through its value.
        let goal = match goal {
            Goal::Known(term) => Goal::Known(self.unfold(&term)?),
            other => other,
        };
        match kind {
            SentenceAstKind::Assume { islands } => {
                let locals = self.assume_locals(sentence, &islands)?;
                let mut current = goal;
                let mut introduced = Vec::new();
                for (spelling, ident_start, ident_end, island) in &locals {
                    let ident = (*ident_start, *ident_end);
                    match current {
                        Goal::Known(Term::Pi { binders, body }) => {
                            let (first, rest) = binders
                                .split_first()
                                .map(|(first, rest)| (first.clone(), rest.to_vec()))
                                .ok_or_else(|| {
                                    fail(code!("LLI9001"), "phase proofs: empty Pi binder group")
                                })?;
                            self.declare_assumed(
                                spelling,
                                first.id,
                                Some(first.ty.clone()),
                                ident,
                                island,
                            );
                            introduced.push(first.id);
                            current = Goal::Known(if rest.is_empty() {
                                *body
                            } else {
                                Term::Pi {
                                    binders: rest,
                                    body,
                                }
                            });
                        }
                        Goal::Known(ref term) if core_head(term) == Some(CoreRef::Not) => {
                            // `Not P` is `P → False`: the assumption has type
                            // `P`; the residual `False` goal has no IR term
                            // and stays unknown (§16.2).
                            let Term::App { explicit_args, .. } = term else {
                                return Err(fail(code!("LLI9001"), "phase proofs: Not head"));
                            };
                            let hypothesis = explicit_args.first().cloned();
                            let id = self.alloc.fresh();
                            self.declare_assumed(spelling, id, hypothesis, ident, island);
                            introduced.push(id);
                            current = Goal::Unknown;
                        }
                        Goal::Known(ref term) if is_closed_shape(term) => {
                            return Err(fail(
                                code!("LLF5002"),
                                "Assume introduces the next leading goal binders, but the goal is not a function type or a negation",
                            )
                            .with_span(sentence_span));
                        }
                        // An unknown goal, or a known goal headed by a
                        // predicate that may unfold to a function type:
                        // introduce an untyped local; Lean is final.
                        Goal::Known(_) | Goal::Unknown | Goal::MaybeClosed => {
                            let id = self.alloc.fresh();
                            self.declare_assumed(spelling, id, None, ident, island);
                            introduced.push(id);
                            current = Goal::Unknown;
                        }
                    }
                }
                // Commas between islands are structural.
                for token in &tokens {
                    if let TextToken::Atom(atom_index) = token {
                        let atom = &self.shared.atoms[*atom_index];
                        if atom.class == AtomClass::AsciiSymbol && atom.text == "," {
                            self.structural_row(*atom_index, "comma");
                        }
                    }
                }
                Ok((Proof::Intro(introduced), current, false))
            }
            SentenceAstKind::Apply { term } => {
                let function = self.term_island(&term, None)?;
                match self.residual_premises(&function, &goal)? {
                    Residuals::Known(premises) if premises.len() == 1 => Ok((
                        Proof::ApplyOne(function.term),
                        premises.into_iter().next().expect("one premise"),
                        false,
                    )),
                    Residuals::Known(premises) => Err(fail(
                        code!("LLF5002"),
                        format!(
                            "simple Apply is valid only when exactly one residual goal remains; this application yields {}{}",
                            premises.len(),
                            if premises.len() > 1 {
                                "; use the structured apply"
                            } else {
                                "; use `Close the goal with`"
                            }
                        ),
                    )
                    .with_span(sentence_span)),
                    // The signature or goal does not determine the residual
                    // premises: Lean is final (§16.1).
                    Residuals::Unknown => {
                        Ok((Proof::ApplyOne(function.term), Goal::Unknown, false))
                    }
                }
            }
            SentenceAstKind::CloseWith { term } => {
                let exact = self.term_against_goal(&term, goal.known())?;
                Ok((Proof::Exact(exact.term), Goal::Unknown, true))
            }
            SentenceAstKind::CloseByReflexivity => {
                if let Some(goal_term) = goal.known() {
                    let rejects = is_closed_shape(goal_term)
                        && !matches!(core_head(goal_term), Some(CoreRef::Eq | CoreRef::Iff));
                    if rejects {
                        return Err(fail(
                            code!("LLF5002"),
                            "reflexivity closes an equality or equivalence goal",
                        )
                        .with_span(sentence_span));
                    }
                }
                Ok((Proof::Reflexivity, Goal::Unknown, true))
            }
            SentenceAstKind::Witness { term } => {
                let Some(goal_term) = goal.known() else {
                    let witness = self.term_island(&term, None)?;
                    return Ok((Proof::Witness(witness.term), Goal::Unknown, false));
                };
                // Unique existence was read through its lowering when the goal
                // was unfolded (§18.4): the residual after the witness is the
                // conjunction of the property and the uniqueness clause.
                match goal_term {
                    Term::App {
                        function,
                        explicit_args,
                        ..
                    } if matches!(
                        &**function,
                        Term::Global(GlobalRef::Core(CoreRef::Exists), _)
                    ) && explicit_args.len() == 1 =>
                    {
                        // §16.2: the witness receives the existential binder's
                        // type as its expected type; a numeral witness is
                        // typed.
                        let lambda = explicit_args[0].clone();
                        let binder_ty = match &lambda {
                            Term::Lambda { binders, .. } => {
                                binders.first().map(|binder| binder.ty.clone())
                            }
                            _ => None,
                        };
                        let witness = self.term_island(&term, binder_ty.as_ref())?;
                        let next =
                            beta(&lambda, std::slice::from_ref(&witness.term), self.budget)?;
                        Ok((Proof::Witness(witness.term), Goal::Known(next), false))
                    }
                    term if is_closed_shape(term) => Err(fail(
                        code!("LLF5002"),
                        "the goal is not an existential; a witness supplies the next existential witness",
                    )
                    .with_span(sentence_span)),
                    // A goal headed by a predicate that may unfold to an
                    // existential: Lean is final.
                    _ => {
                        let witness = self.term_island(&term, None)?;
                        Ok((Proof::Witness(witness.term), Goal::Unknown, false))
                    }
                }
            }
            SentenceAstKind::SelectLeft | SentenceAstKind::SelectRight => {
                let left = matches!(kind, SentenceAstKind::SelectLeft);
                let step = if left {
                    Proof::SelectLeft
                } else {
                    Proof::SelectRight
                };
                let Some(goal_term) = goal.known() else {
                    return Ok((step, Goal::Unknown, false));
                };
                match goal_term {
                    Term::App {
                        function,
                        explicit_args,
                        ..
                    } if matches!(&**function, Term::Global(GlobalRef::Core(CoreRef::Or), _))
                        && explicit_args.len() == 2 =>
                    {
                        let next = explicit_args[usize::from(!left)].clone();
                        Ok((step, Goal::Known(next), false))
                    }
                    term if is_closed_shape(term) => Err(fail(
                        code!("LLF5002"),
                        "the goal is not a disjunction; selecting an alternative chooses `Or.inl` or `Or.inr`",
                    )
                    .with_span(sentence_span)),
                    // A goal headed by a predicate that may unfold to a
                    // disjunction: Lean is final.
                    _ => Ok((step, Goal::Unknown, false)),
                }
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn cases_like(
        &mut self,
        induction: bool,
        scrutinee: &BraceArg,
        cases: &[CaseAst],
        goal: &Goal,
        begin: usize,
    ) -> Result<Proof, Diagnostic> {
        let mut scrutinee_term = self.term_brace(scrutinee)?;
        // A hypothesis whose type is a document or defined predicate is
        // eliminated through its definition (as Lean's `cases` unfolds it):
        // the descriptor is looked up on the unfolded head.
        if let Some(ty) = scrutinee_term.ty.take() {
            scrutinee_term.ty = Some(self.unfold(&ty)?);
        }
        // The scrutinee type must carry a validated eliminator descriptor
        // (§16.8, GL-14).
        let Some((type_entry, eliminator)) = scrutinee_term
            .ty
            .as_ref()
            .and_then(|ty| self.descriptor_for_type(ty))
        else {
            return Err(fail(
                code!("LLF5002"),
                match &scrutinee_term.ty {
                    Some(_) => "the scrutinee type has no glossary eliminator descriptor",
                    None => "the scrutinee type is not statically known, so no glossary eliminator descriptor applies",
                },
            )
            .with_span(self.span_of(scrutinee.range)));
        };
        let Some(scrutinee_ty) = scrutinee_term.ty.clone() else {
            return Err(fail(
                code!("LLI9001"),
                "phase proofs: descriptor without a type",
            ));
        };
        // Every constructor exactly once; order canonicalizes to descriptor
        // order (§16.8).
        let mut ordered: Vec<Option<&CaseAst>> = vec![None; eliminator.constructors.len()];
        for case in cases {
            let Some(position) = eliminator
                .constructors
                .iter()
                .position(|constructor| constructor.entry.to_string() == case.entry.text)
            else {
                return Err(fail(
                    code!("LLF5003"),
                    format!(
                        "`{}` is not a constructor of `{type_entry}`",
                        case.entry.text
                    ),
                )
                .with_span(self.span_of(case.entry.range)));
            };
            if ordered[position].is_some() {
                return Err(fail(
                    code!("LLF5003"),
                    format!("constructor `{}` appears twice", case.entry.text),
                )
                .with_span(self.span_of(case.entry.range)));
            }
            ordered[position] = Some(case);
        }
        let scrutinee_local = match &scrutinee_term.term {
            Term::Local(id) => Some(*id),
            _ => None,
        };
        let mut ir_cases = Vec::new();
        for (constructor, slot) in eliminator.constructors.iter().zip(&ordered) {
            let Some(case) = slot else {
                return Err(fail(
                    code!("LLF5003"),
                    format!("constructor `{}` has no case", constructor.entry),
                )
                .with_span(self.span_of((begin, begin + 1))));
            };
            let expected: usize = constructor.fields.len()
                + if induction {
                    constructor.induction_hypotheses.len()
                } else {
                    0
                };
            if case.binds.len() != expected {
                return Err(fail(
                    code!("LLF5003"),
                    format!(
                        "constructor `{}` binds {expected} locals, found {}",
                        constructor.entry,
                        case.binds.len()
                    ),
                )
                .with_span(self.span_of(case.bind_arg.range)));
            }
            // Field types come from the constructor entry's explicit binders
            // instantiated against the scrutinee type; the constructor
            // application over the fresh field locals specializes the goal
            // (§16.8, §16.9).
            let instance = self.constructor_instance(&constructor.entry, &scrutinee_ty);
            let field_ids: Vec<LocalId> = constructor
                .fields
                .iter()
                .map(|_| self.alloc.fresh())
                .collect();
            let mut field_types: Vec<Option<Term>> = vec![None; constructor.fields.len()];
            let mut constructor_app: Option<Term> = None;
            if let Some((global, instantiated)) = &instance {
                let explicit_count = instantiated
                    .binders
                    .iter()
                    .filter(|(binder, _)| binder.mode == BinderMode::Explicit)
                    .count();
                if explicit_count == constructor.fields.len() {
                    let mut map: BTreeMap<LocalId, Term> = BTreeMap::new();
                    let mut omitted = Vec::new();
                    let mut field_index = 0usize;
                    for (ordinal, (binder, meta)) in instantiated.binders.iter().enumerate() {
                        match binder.mode {
                            BinderMode::Explicit => {
                                // The field type read through its definitions
                                // and beta-reduced (a proof field typed by an
                                // instantiated predicate `p w` with `p := fun
                                // x => P x` is `P w`).
                                let ty = instantiated
                                    .binder_type(ordinal)
                                    .map(|ty| self.unfold(&subst(&ty, &map)))
                                    .transpose()?;
                                field_types[field_index] = ty;
                                map.insert(*meta, Term::Local(field_ids[field_index]));
                                field_index += 1;
                            }
                            BinderMode::Implicit | BinderMode::Instance => {
                                omitted.push(ImplicitBinderId(
                                    u32::try_from(ordinal).unwrap_or(u32::MAX),
                                ));
                            }
                        }
                    }
                    let head = Term::Global(global.clone(), Vec::new());
                    constructor_app = Some(if field_ids.is_empty() {
                        head
                    } else {
                        Term::App {
                            function: Box::new(head),
                            explicit_args: field_ids.iter().map(|id| Term::Local(*id)).collect(),
                            omitted_implicit_binders: omitted,
                        }
                    });
                }
            }
            // The branch goal: the goal with the scrutinee local replaced by
            // the constructor application; unknown otherwise.
            let branch_goal = match (goal.known(), scrutinee_local, &constructor_app) {
                (Some(goal_term), Some(local), Some(application)) => {
                    let mut map = BTreeMap::new();
                    map.insert(local, application.clone());
                    Goal::Known(subst(goal_term, &map))
                }
                _ => Goal::Unknown,
            };
            // Induction hypotheses: one per recursive field (a field whose
            // type is the scrutinee type), in descriptor order, typed by the
            // goal at that field.
            let recursive_fields: Vec<usize> = field_types
                .iter()
                .enumerate()
                .filter(|(_, ty)| {
                    ty.as_ref()
                        .is_some_and(|ty| ty.eq_key() == scrutinee_ty.eq_key())
                })
                .map(|(index, _)| index)
                .collect();
            let ih_types: Vec<Option<Term>> = constructor
                .induction_hypotheses
                .iter()
                .enumerate()
                .map(|(position, _)| {
                    if recursive_fields.len() != constructor.induction_hypotheses.len() {
                        return None;
                    }
                    let field = *recursive_fields.get(position)?;
                    let goal_term = goal.known()?;
                    let local = scrutinee_local?;
                    let mut map = BTreeMap::new();
                    map.insert(local, Term::Local(field_ids[field]));
                    Some(subst(goal_term, &map))
                })
                .collect();
            self.scopes.push_frame();
            let mut binders: Vec<(LocalId, String)> = Vec::new();
            for (position, spelling) in case.binds.iter().enumerate() {
                if !crate::lexicon::lse::is_lse_identifier(spelling)
                    || !self.scopes.is_fresh(spelling)
                    || binders.iter().any(|(_, existing)| existing == spelling)
                {
                    self.scopes.pop_frame();
                    return Err(fail(
                        code!("LLF5003"),
                        format!("`{spelling}` is not a fresh local spelling"),
                    )
                    .with_span(self.span_of(case.bind_arg.range)));
                }
                let (id, ty) = if position < field_ids.len() {
                    (field_ids[position], field_types[position].clone())
                } else {
                    (
                        self.alloc.fresh(),
                        ih_types.get(position - field_ids.len()).cloned().flatten(),
                    )
                };
                self.scopes.declare(spelling, id, ty);
                self.spellings.insert(id, spelling.clone());
                binders.push((id, spelling.clone()));
            }
            let proof = self.elab_env(&case.proof, branch_goal);
            self.scopes.pop_frame();
            ir_cases.push(CaseProof {
                constructor: constructor.entry.clone(),
                lean_name: constructor.lean_name.clone(),
                binders,
                proof: proof?,
            });
        }
        Ok(if induction {
            Proof::Induction {
                scrutinee: scrutinee_term.term,
                cases: ir_cases,
            }
        } else {
            Proof::Cases {
                scrutinee: scrutinee_term.term,
                cases: ir_cases,
            }
        })
    }

    /// Do a goal endpoint and a chain term denote one term up to
    /// alpha-renaming and definition unfolding (§16.10)?
    fn endpoints_match(&mut self, goal_side: &Term, chain_side: &Term) -> Result<bool, Diagnostic> {
        if goal_side.eq_key() == chain_side.eq_key() {
            return Ok(true);
        }
        let (goal_side, chain_side) = (self.unfold(goal_side)?, self.unfold(chain_side)?);
        Ok(unify_closed(&goal_side, &chain_side))
    }

    fn calculate(
        &mut self,
        start: &BraceArg,
        steps: &[crate::grammar::structural::CalcStepAst],
        goal: &Goal,
    ) -> Result<Proof, Diagnostic> {
        // Every relation entry is identical and carries a calculation
        // descriptor (§16.10).
        let first_relation = &steps[0].relation.text;
        for step in steps {
            if step.relation.text != *first_relation {
                return Err(fail(
                    code!("LLF5003"),
                    "every relation entry in a calculation is identical",
                )
                .with_span(self.span_of(step.relation.range)));
            }
        }
        let qualified = QualifiedId::parse(first_relation).map_err(|reason| {
            fail(code!("LLR3005"), reason).with_span(self.span_of(steps[0].relation.range))
        })?;
        let entry = self.shared.closure.entry(&qualified).ok_or_else(|| {
            fail(
                code!("LLR3005"),
                format!("`{qualified}` is not in the glossary closure"),
            )
            .with_span(self.span_of(steps[0].relation.range))
        })?;
        if !entry.calculation {
            return Err(fail(
                code!("LLF5002"),
                format!("`{qualified}` has no glossary calculation descriptor"),
            )
            .with_span(self.span_of(steps[0].relation.range)));
        }
        let relation = crate::elaborate::expressions::global_for_entry(self.shared, &qualified)
            .map_err(|reason| {
                fail(code!("LLR3005"), reason).with_span(self.span_of(steps[0].relation.range))
            })?;
        let start_term = self.term_brace(start)?;
        // §16.10: every chain term has the start term's type; a numeral
        // step term is typed by the chain.
        let chain_ty = start_term.ty.clone();
        let mut ir_steps = Vec::new();
        for step in steps {
            let term = self.term_brace_expected(&step.term, chain_ty.as_ref())?;
            let proof = self.term_brace(&step.proof)?;
            ir_steps.push(CalculationStep {
                term: term.term,
                proof: proof.term,
            });
        }
        // The first and last terms match the goal's endpoints when the goal
        // is statically known (§16.10).
        if let Some(Term::App {
            function,
            explicit_args,
            ..
        }) = goal.known()
        {
            let goal_relation_matches = matches!(
                (&**function, &relation),
                (Term::Global(g, _), r) if g == r
            );
            if goal_relation_matches && explicit_args.len() == 2 {
                // Endpoints match up to alpha-renaming and definition
                // unfolding (§16.10): a term spelled through a noun-of entry
                // and its math form, or a definition and its body, are one
                // endpoint; distinct free locals are not.
                let (goal_left, goal_right) = (explicit_args[0].clone(), explicit_args[1].clone());
                let last = ir_steps.last().map(|step| step.term.clone());
                let left_ok = self.endpoints_match(&goal_left, &start_term.term)?;
                let right_ok = match last {
                    Some(last) => self.endpoints_match(&goal_right, &last)?,
                    None => false,
                };
                if !left_ok || !right_ok {
                    return Err(fail(
                        code!("LLF5002"),
                        "the first and last terms must match the current goal's endpoints",
                    )
                    .with_span(self.span_of(start.range)));
                }
            }
        }
        Ok(Proof::Calculate {
            relation,
            start: start_term.term,
            steps: ir_steps,
        })
    }
}
