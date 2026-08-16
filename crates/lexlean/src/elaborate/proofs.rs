//! Structured proof elaboration (SPEC.md §16): conservative goal tracking
//! over the closed proof IR. Lean elaboration is final (§16.1); LexLean
//! rejects only what is statically certain to be malformed and never
//! accepts a form outside the registered set.

use std::collections::BTreeMap;

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::elaborate::expressions::{beta1, subst, ElabTerm, ExprElab};
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
use crate::ir::term::{CoreRef, GlobalRef, LocalId, Term};
use crate::lexicon::lse::QualifiedId;
use crate::source::atom::AtomClass;
use crate::source::coverage::{Origin, SourceRow};
use crate::source::scan::compose_identifier;

/// The conservative goal state: `None` after a transformation whose result
/// LexLean cannot compute (rewrite, simplify, branch specialization).
type Goal = Option<Term>;

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
}

fn fail(code: crate::diagnostic::DiagnosticCode, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code, message)
}

impl<'a, 'b> ProofElab<'a, 'b> {
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

    fn term_island(
        &mut self,
        token: &TextToken,
        expected: Option<&Term>,
    ) -> Result<ElabTerm, Diagnostic> {
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

    /// A brace argument that holds one mathematical term (§16.4–§16.10).
    fn term_brace(&mut self, arg: &BraceArg) -> Result<ElabTerm, Diagnostic> {
        self.term_brace_expected(arg, None)
    }

    fn term_brace_expected(
        &mut self,
        arg: &BraceArg,
        expected: Option<&Term>,
    ) -> Result<ElabTerm, Diagnostic> {
        let ast = parse_math(
            self.shared.path,
            self.shared.atoms,
            arg.range,
            self.shared.closure,
            self.shared.visible,
            self.budget,
        )?;
        let mut elaborator = ExprElab {
            shared: self.shared,
            scopes: self.scopes,
            alloc: self.alloc,
            budget: self.budget,
        };
        let result = elaborator.elaborate(&ast, expected)?;
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
        let result = self.elab_items(&env.items, goal);
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
    ) -> Result<Vec<Proof>, Diagnostic> {
        let mut steps: Vec<Proof> = Vec::new();
        let mut closed = false;
        for item in items {
            if closed {
                return Err(fail(
                    code!("LLF5002"),
                    "a proof step after the current branch has closed",
                ));
            }
            match item {
                ProofItemAst::Sentence(sentence) => {
                    let (step, next_goal, now_closed) = self.simple_sentence(sentence, goal)?;
                    steps.push(step);
                    goal = next_goal;
                    closed = now_closed;
                }
                ProofItemAst::Have {
                    name,
                    proposition,
                    proof,
                } => {
                    if !self.scopes.is_fresh(&name.text) {
                        return Err(fail(
                            code!("LLF5002"),
                            format!("`{}` is not fresh in the current proof scope", name.text),
                        )
                        .with_span(self.span_of(name.range)));
                    }
                    let prop_term = self.proposition_sentence(proposition)?;
                    // The nested proof cannot see the hypothesis (§16.3).
                    let nested = self.elab_env(proof, Some(prop_term.clone()))?;
                    let local = self.alloc.fresh();
                    self.scopes
                        .declare(&name.text, local, Some(prop_term.clone()));
                    self.spellings.insert(local, name.text.clone());
                    steps.push(Proof::Have {
                        local,
                        proposition: prop_term,
                        proof: Box::new(nested),
                    });
                }
                ProofItemAst::Rewrite { target, rules } => {
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
                    match &rewrite_target {
                        RewriteTarget::Goal => goal = None,
                        RewriteTarget::Hypothesis(id) => self.scopes.forget_type(*id),
                    }
                    steps.push(Proof::Rewrite {
                        target: rewrite_target,
                        rules: ir_rules,
                    });
                }
                ProofItemAst::Simplify { target, rules } => {
                    let rewrite_target = self.rewrite_target(target)?;
                    let mut ir_rules = Vec::new();
                    for rule in rules {
                        ir_rules.push(self.term_brace(rule)?.term);
                    }
                    match &rewrite_target {
                        RewriteTarget::Goal => goal = None,
                        RewriteTarget::Hypothesis(id) => self.scopes.forget_type(*id),
                    }
                    steps.push(Proof::SimplifyOnly {
                        target: rewrite_target,
                        rules: ir_rules,
                    });
                }
                ProofItemAst::Apply { function, premises } => {
                    let function_term = self.term_brace(function)?;
                    let residuals = self.residual_premises(&function_term, &goal);
                    // Premise labels are consecutive decimal integers from 1
                    // and every residual premise occurs exactly once (§16.6).
                    for (index, (label, _)) in premises.iter().enumerate() {
                        if *label != (index as u64) + 1 {
                            return Err(fail(
                                code!("LLF5003"),
                                "premise labels are consecutive decimal integers beginning with 1",
                            ));
                        }
                    }
                    if let Some(expected) = &residuals {
                        if expected.len() != premises.len() {
                            return Err(fail(
                                code!("LLF5003"),
                                format!(
                                    "the applied signature yields {} residual premises, found {}",
                                    expected.len(),
                                    premises.len()
                                ),
                            ));
                        }
                    }
                    let mut premise_proofs = Vec::new();
                    for (index, (_, body)) in premises.iter().enumerate() {
                        let premise_goal = residuals
                            .as_ref()
                            .and_then(|expected| expected.get(index).cloned());
                        premise_proofs.push(self.elab_env(body, premise_goal)?);
                    }
                    steps.push(Proof::Apply {
                        function: function_term.term,
                        premises: premise_proofs,
                    });
                    closed = true;
                }
                ProofItemAst::Constructor { branches } => {
                    for (index, (label, _)) in branches.iter().enumerate() {
                        if *label != (index as u64) + 1 {
                            return Err(fail(
                                code!("LLF5003"),
                                "branch labels are consecutive decimal integers beginning with 1",
                            ));
                        }
                    }
                    let branch_goals: Option<Vec<Term>> = match &goal {
                        Some(term) => {
                            let fields = self.constructor_fields(term);
                            if fields.is_none() {
                                // §16.7: a statically known goal must be a
                                // core constructor target.
                                return Err(fail(
                                    code!("LLF5002"),
                                    "the goal is not a constructor target",
                                ));
                            }
                            fields
                        }
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
                            ));
                        }
                    }
                    let mut branch_proofs = Vec::new();
                    for (index, (_, body)) in branches.iter().enumerate() {
                        let branch_goal = branch_goals
                            .as_ref()
                            .and_then(|expected| expected.get(index).cloned());
                        branch_proofs.push(self.elab_env(body, branch_goal)?);
                    }
                    steps.push(Proof::Constructor(branch_proofs));
                    closed = true;
                }
                ProofItemAst::CasesLike {
                    induction,
                    scrutinee,
                    cases,
                } => {
                    let step = self.cases_like(*induction, scrutinee, cases)?;
                    steps.push(step);
                    closed = true;
                }
                ProofItemAst::Calculate { start, steps: calc } => {
                    let step = self.calculate(start, calc, &goal)?;
                    steps.push(step);
                    closed = true;
                }
            }
        }
        if !closed {
            return Err(fail(code!("LLF5004"), "the proof does not close all goals"));
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

    fn rewrite_target(&mut self, target: &BraceArg) -> Result<RewriteTarget, Diagnostic> {
        if target.text == "goal" {
            return Ok(RewriteTarget::Goal);
        }
        match self.scopes.lookup(&target.text) {
            Some(entry) => Ok(RewriteTarget::Hypothesis(entry.id)),
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

    fn check_equation_shaped(&self, term: &ElabTerm, arg: &BraceArg) -> Result<(), Diagnostic> {
        // A rule term must prove an equality or equivalence when its type
        // is statically known (§16.4). Unknown types defer to Lean.
        let Some(ty) = &term.ty else {
            return Ok(());
        };
        let mut probe = ty;
        while let Term::Pi { body, .. } = probe {
            probe = body;
        }
        if let Term::App { function, .. } = probe {
            if let Term::Global(GlobalRef::Core(CoreRef::Eq | CoreRef::Iff), _) = &**function {
                return Ok(());
            }
        }
        Err(fail(
            code!("LLF5002"),
            "a rewrite rule proves an equality or equivalence",
        )
        .with_span(self.span_of(arg.range)))
    }

    /// The residual explicit premises of applying a proof term to the
    /// current goal (§16.2, §16.6), when the signature and goal suffice.
    fn residual_premises(&self, function: &ElabTerm, goal: &Goal) -> Option<Vec<Term>> {
        let ty = function.ty.as_ref()?;
        let goal_term = goal.as_ref()?;
        let Term::Pi { binders, body } = ty else {
            return Some(Vec::new());
        };
        // Conservative: the conclusion must be syntactically the goal after
        // substituting no binder (dependent conclusions defer to Lean).
        if body.as_ref().canonical_key() != goal_term.canonical_key() {
            return None;
        }
        Some(
            binders
                .iter()
                .filter(|binder| matches!(binder.mode, crate::lexicon::lse::BinderMode::Explicit))
                .map(|binder| binder.ty.clone())
                .collect(),
        )
    }

    fn constructor_fields(&self, goal: &Term) -> Option<Vec<Term>> {
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
                            return Some(explicit_args.clone());
                        }
                    }
                    CoreRef::Iff => {
                        if let [left, right] = explicit_args.as_slice() {
                            let forward = Term::Pi {
                                binders: vec![crate::ir::term::Binder {
                                    id: LocalId(u64::MAX - 1),
                                    mode: crate::lexicon::lse::BinderMode::Explicit,
                                    ty: left.clone(),
                                    spelling: String::new(),
                                }],
                                body: Box::new(right.clone()),
                            };
                            let backward = Term::Pi {
                                binders: vec![crate::ir::term::Binder {
                                    id: LocalId(u64::MAX - 2),
                                    mode: crate::lexicon::lse::BinderMode::Explicit,
                                    ty: right.clone(),
                                    spelling: String::new(),
                                }],
                                body: Box::new(left.clone()),
                            };
                            return Some(vec![forward, backward]);
                        }
                    }
                    _ => {}
                }
            }
        }
        None
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
        };
        let ProofSentence { kind, keywords } = parse_proof_sentence(&parser)?;
        for keyword in &keywords {
            self.structural_row(keyword.atom, keyword.entry);
        }
        self.structural_row(sentence.period, "period");
        match kind {
            SentenceAstKind::Assume { islands } => {
                let Some(mut current) = goal else {
                    return Err(fail(
                        code!("LLF5002"),
                        "Assume needs a statically known goal shape here",
                    )
                    .with_span(self.span_of(sentence.range)));
                };
                let mut introduced = Vec::new();
                for island in &islands {
                    let TextToken::Island {
                        inner_start,
                        inner_end,
                        ..
                    } = island
                    else {
                        continue;
                    };
                    let mut index = *inner_start;
                    while index < *inner_end
                        && self.shared.atoms[index].class == AtomClass::Whitespace
                    {
                        index += 1;
                    }
                    let Some((spelling, ident_end)) = compose_identifier(self.shared.atoms, index)
                    else {
                        return Err(fail(
                            code!("LLF5002"),
                            "Assume introduces fresh local identifiers",
                        )
                        .with_span(self.span_of(sentence.range)));
                    };
                    if !self.scopes.is_fresh(&spelling) {
                        return Err(fail(
                            code!("LLF5002"),
                            format!("`{spelling}` is not fresh in the current proof scope"),
                        )
                        .with_span(self.span_of((index, ident_end))));
                    }
                    let Term::Pi { binders, body } = current else {
                        return Err(fail(
                            code!("LLF5002"),
                            "Assume introduces the next leading goal binders, but the goal is not a function type",
                        )
                        .with_span(self.span_of(sentence.range)));
                    };
                    let (first, rest) = binders
                        .split_first()
                        .map(|(first, rest)| (first.clone(), rest.to_vec()))
                        .ok_or_else(|| {
                            fail(code!("LLI9001"), "phase proofs: empty Pi binder group")
                        })?;
                    self.scopes
                        .declare(&spelling, first.id, Some(first.ty.clone()));
                    self.spellings.insert(first.id, spelling.clone());
                    // Coverage for the introduced local and its island.
                    if let TextToken::Island { .. } = island {
                        let mut rows = Vec::new();
                        crate::elaborate::island_delim_rows_public(self.shared, island, &mut rows);
                        self.rows.extend(rows);
                    }
                    let ident_first = &self.shared.atoms[index];
                    self.rows.push(SourceRow {
                        path: self.shared.path.to_owned(),
                        byte_start: ident_first.byte_start,
                        byte_end: self.shared.atoms[ident_end - 1].byte_end,
                        class: AtomClass::Word,
                        binding: Origin::Local(first.id.0 as usize),
                    });
                    introduced.push(first.id);
                    current = if rest.is_empty() {
                        *body
                    } else {
                        Term::Pi {
                            binders: rest,
                            body,
                        }
                    };
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
                Ok((Proof::Intro(introduced), Some(current), false))
            }
            SentenceAstKind::Apply { term } => {
                let function = self.term_island(&term, None)?;
                let residuals = self.residual_premises(&function, &goal);
                match residuals {
                    Some(premises) if premises.len() == 1 => Ok((
                        Proof::ApplyOne(function.term),
                        Some(premises.into_iter().next().expect("one premise")),
                        false,
                    )),
                    Some(premises) => Err(fail(
                        code!("LLF5002"),
                        format!(
                            "simple Apply is valid only when exactly one residual goal remains; this application yields {}",
                            premises.len()
                        ),
                    )
                    .with_span(self.span_of(sentence.range))),
                    None => Err(fail(
                        code!("LLF5002"),
                        "the applied signature and goal do not determine the residual premises; use the structured apply",
                    )
                    .with_span(self.span_of(sentence.range))),
                }
            }
            SentenceAstKind::CloseWith { term } => {
                let exact = self.term_island(&term, goal.as_ref())?;
                Ok((Proof::Exact(exact.term), None, true))
            }
            SentenceAstKind::CloseByReflexivity => {
                if let Some(goal_term) = &goal {
                    let mut head = goal_term;
                    if let Term::App { function, .. } = head {
                        head = function;
                    }
                    if !matches!(
                        head,
                        Term::Global(GlobalRef::Core(CoreRef::Eq | CoreRef::Iff), _)
                    ) {
                        return Err(fail(
                            code!("LLF5002"),
                            "reflexivity closes an equality or equivalence goal",
                        )
                        .with_span(self.span_of(sentence.range)));
                    }
                }
                Ok((Proof::Reflexivity, None, true))
            }
            SentenceAstKind::Witness { term } => {
                let Some(goal_term) = &goal else {
                    return Err(fail(
                        code!("LLF5002"),
                        "a witness needs a statically known existential goal",
                    )
                    .with_span(self.span_of(sentence.range)));
                };
                let Term::App {
                    function,
                    explicit_args,
                    ..
                } = goal_term
                else {
                    return Err(fail(code!("LLF5002"), "the goal is not an existential")
                        .with_span(self.span_of(sentence.range)));
                };
                if !matches!(
                    &**function,
                    Term::Global(GlobalRef::Core(CoreRef::Exists | CoreRef::ExistsUnique), _)
                ) || explicit_args.len() != 1
                {
                    return Err(fail(code!("LLF5002"), "the goal is not an existential")
                        .with_span(self.span_of(sentence.range)));
                }
                // §16.2: the witness receives the existential binder's
                // type as its expected type; a numeral witness is typed.
                let expected = match &explicit_args[0] {
                    Term::Lambda { binders, .. } => binders.first().map(|binder| binder.ty.clone()),
                    _ => None,
                };
                let witness = self.term_island(&term, expected.as_ref())?;
                let next = beta1(&explicit_args[0], &witness.term);
                Ok((Proof::Witness(witness.term), Some(next), false))
            }
            SentenceAstKind::SelectLeft | SentenceAstKind::SelectRight => {
                let left = matches!(kind, SentenceAstKind::SelectLeft);
                let Some(goal_term) = &goal else {
                    return Err(fail(
                        code!("LLF5002"),
                        "selecting an alternative needs a statically known disjunction goal",
                    )
                    .with_span(self.span_of(sentence.range)));
                };
                let Term::App {
                    function,
                    explicit_args,
                    ..
                } = goal_term
                else {
                    return Err(fail(code!("LLF5002"), "the goal is not a disjunction")
                        .with_span(self.span_of(sentence.range)));
                };
                if !matches!(&**function, Term::Global(GlobalRef::Core(CoreRef::Or), _))
                    || explicit_args.len() != 2
                {
                    return Err(fail(code!("LLF5002"), "the goal is not a disjunction")
                        .with_span(self.span_of(sentence.range)));
                }
                let next = explicit_args[usize::from(!left)].clone();
                Ok((
                    if left {
                        Proof::SelectLeft
                    } else {
                        Proof::SelectRight
                    },
                    Some(next),
                    false,
                ))
            }
        }
    }

    fn cases_like(
        &mut self,
        induction: bool,
        scrutinee: &BraceArg,
        cases: &[CaseAst],
    ) -> Result<Proof, Diagnostic> {
        let scrutinee_term = self.term_brace(scrutinee)?;
        // The scrutinee type must carry a validated eliminator descriptor
        // (§16.8, GL-14).
        let descriptor_entry = scrutinee_term.ty.as_ref().and_then(|ty| {
            let head: &Term = match ty {
                Term::App { function, .. } => function,
                other => other,
            };
            if let Term::Global(GlobalRef::External(external), _) = head {
                let qualified = QualifiedId::parse(&external.entry).ok()?;
                self.shared.closure.entry(&qualified)
            } else if let Term::Global(GlobalRef::DefinedLexicon(defined), _) = head {
                let qualified = QualifiedId::parse(&defined.entry).ok()?;
                self.shared.closure.entry(&qualified)
            } else {
                None
            }
        });
        let Some(eliminator) = descriptor_entry.and_then(|entry| entry.eliminator.as_ref()) else {
            return Err(fail(
                code!("LLF5002"),
                "the scrutinee type has no glossary eliminator descriptor",
            )
            .with_span(self.span_of(scrutinee.range)));
        };
        let eliminator = eliminator.clone();
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
                        "`{}` is not a constructor of the scrutinee type",
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
        let mut ir_cases = Vec::new();
        for (constructor, slot) in eliminator.constructors.iter().zip(&ordered) {
            let Some(case) = slot else {
                return Err(fail(
                    code!("LLF5003"),
                    format!("constructor `{}` has no case", constructor.entry),
                ));
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
            self.scopes.push_frame();
            let mut binders = Vec::new();
            for spelling in &case.binds {
                if !crate::lexicon::lse::is_lse_identifier(spelling)
                    || !self.scopes.is_fresh(spelling)
                {
                    self.scopes.pop_frame();
                    return Err(fail(
                        code!("LLF5003"),
                        format!("`{spelling}` is not a fresh local spelling"),
                    )
                    .with_span(self.span_of(case.bind_arg.range)));
                }
                let id = self.alloc.fresh();
                // Branch binder types are not statically known.
                self.scopes.declare(spelling, id, None);
                binders.push((id, spelling.clone()));
            }
            // Branch goals are constructor-specialized and not statically
            // known; Lean elaboration is final (§16.1).
            let proof = self.elab_env(&case.proof, None);
            self.scopes.pop_frame();
            ir_cases.push(CaseProof {
                constructor: QualifiedId::parse(&constructor.entry.to_string())
                    .map_err(|reason| fail(code!("LLI9001"), reason))?,
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
            .map_err(|reason| fail(code!("LLR3005"), reason))?;
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
        {
            if let Some(Term::App {
                function,
                explicit_args,
                ..
            }) = goal
            {
                let goal_relation_matches = matches!(
                    (&**function, &relation),
                    (Term::Global(g, _), r) if g == r
                );
                if goal_relation_matches && explicit_args.len() == 2 {
                    let left_ok =
                        explicit_args[0].canonical_key() == start_term.term.canonical_key();
                    let right_ok = ir_steps
                        .last()
                        .map(|step| explicit_args[1].canonical_key() == step.term.canonical_key())
                        .unwrap_or(false);
                    if !left_ok || !right_ok {
                        return Err(fail(
                            code!("LLF5002"),
                            "the first and last terms must match the current goal's endpoints",
                        )
                        .with_span(self.span_of(start.range)));
                    }
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

/// A minimal substitution shim used when goals specialize.
#[must_use]
pub fn substitute_map(term: &Term, map: &BTreeMap<LocalId, Term>) -> Term {
    subst(term, map)
}
