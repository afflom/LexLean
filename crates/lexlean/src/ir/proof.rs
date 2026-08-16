//! Proof IR (SPEC.md §17.4): exactly the closed variants. No custom, raw,
//! plugin, or unknown variant exists.

use crate::artifact::canonical_json::Json;
use crate::ir::term::{LocalId, Renumber, Term};
use crate::lexicon::lse::QualifiedId;

/// One step in a proof sequence.
pub type ProofStep = Proof;

/// A rewrite or simplify target (§16.4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RewriteTarget {
    /// The current goal.
    Goal,
    /// One in-scope proof local.
    Hypothesis(LocalId),
}

/// One explicitly directed rewrite rule (§16.4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteRule {
    /// `false` for `\forward`, `true` for `\backward`.
    pub reverse: bool,
    /// The one proof term.
    pub term: Term,
}

/// One case branch of `cases` or `induction` (§16.8, §16.9).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseProof {
    /// The constructor's glossary entry.
    pub constructor: QualifiedId,
    /// The constructor's Lean name from the eliminator descriptor.
    pub lean_name: String,
    /// Bound field locals, then induction-hypothesis locals, in descriptor
    /// order.
    pub binders: Vec<(LocalId, String)>,
    /// The branch proof.
    pub proof: Proof,
}

/// One calculation step (§16.10).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CalculationStep {
    /// The next term in the chain.
    pub term: Term,
    /// The proof of the relation from the previous term to this one.
    pub proof: Term,
}

/// The closed proof IR (§17.4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Proof {
    /// A sequence of steps.
    Sequence(Vec<ProofStep>),
    /// `Assume ...`: introduce leading goal binders.
    Intro(Vec<LocalId>),
    /// `Close the goal with TERM.`
    Exact(Term),
    /// `Apply TERM.` with exactly one residual premise.
    ApplyOne(Term),
    /// Structured apply with one nested proof per residual premise.
    Apply {
        /// The applied proof term.
        function: Term,
        /// The premise proofs, in signature order.
        premises: Vec<Proof>,
    },
    /// `Close the goal by reflexivity.`
    Reflexivity,
    /// `Use TERM as the witness.`
    Witness(Term),
    /// `Select the left alternative.`
    SelectLeft,
    /// `Select the right alternative.`
    SelectRight,
    /// A `have` with its nested proof.
    Have {
        /// The introduced hypothesis.
        local: LocalId,
        /// The established proposition.
        proposition: Term,
        /// The nested proof.
        proof: Box<Proof>,
    },
    /// An ordered, explicitly directed rewrite.
    Rewrite {
        /// The one target.
        target: RewriteTarget,
        /// The rules, in source order.
        rules: Vec<RewriteRule>,
    },
    /// `simp only` with exactly the listed rules.
    SimplifyOnly {
        /// The one target.
        target: RewriteTarget,
        /// The listed rules.
        rules: Vec<Term>,
    },
    /// A constructor split with one proof per field.
    Constructor(Vec<Proof>),
    /// Case analysis over a descriptor.
    Cases {
        /// The scrutinee.
        scrutinee: Term,
        /// One branch per constructor, in descriptor order.
        cases: Vec<CaseProof>,
    },
    /// Induction over a descriptor.
    Induction {
        /// The scrutinee.
        scrutinee: Term,
        /// One branch per constructor, in descriptor order.
        cases: Vec<CaseProof>,
    },
    /// A calculation chain.
    Calculate {
        /// The one relation.
        relation: crate::ir::term::GlobalRef,
        /// The starting term.
        start: Term,
        /// The steps.
        steps: Vec<CalculationStep>,
    },
}

impl Proof {
    /// Canonical, alpha-safe JSON (§17.9).
    #[must_use]
    #[allow(clippy::too_many_lines)]
    pub fn to_json(&self, renumber: &mut Renumber) -> Json {
        let tag = |name: &str| ("k", Json::Str(name.to_owned()));
        match self {
            Self::Sequence(steps) => Json::object(vec![
                tag("seq"),
                (
                    "s",
                    Json::Arr(steps.iter().map(|step| step.to_json(renumber)).collect()),
                ),
            ]),
            Self::Intro(locals) => Json::object(vec![
                tag("intro"),
                (
                    "l",
                    Json::Arr(
                        locals
                            .iter()
                            .map(|local| Json::from_usize(renumber.bind(*local)))
                            .collect(),
                    ),
                ),
            ]),
            Self::Exact(term) => Json::object(vec![tag("exact"), ("t", term.to_json(renumber))]),
            Self::ApplyOne(term) => {
                Json::object(vec![tag("apply-one"), ("t", term.to_json(renumber))])
            }
            Self::Apply { function, premises } => Json::object(vec![
                tag("apply"),
                ("f", function.to_json(renumber)),
                (
                    "p",
                    Json::Arr(
                        premises
                            .iter()
                            .map(|premise| premise.to_json(renumber))
                            .collect(),
                    ),
                ),
            ]),
            Self::Reflexivity => Json::object(vec![tag("rfl")]),
            Self::Witness(term) => {
                Json::object(vec![tag("witness"), ("t", term.to_json(renumber))])
            }
            Self::SelectLeft => Json::object(vec![tag("left")]),
            Self::SelectRight => Json::object(vec![tag("right")]),
            Self::Have {
                local,
                proposition,
                proof,
            } => {
                let proposition_json = proposition.to_json(renumber);
                let index = renumber.bind(*local);
                Json::object(vec![
                    tag("have"),
                    ("l", Json::from_usize(index)),
                    ("p", proposition_json),
                    ("q", proof.to_json(renumber)),
                ])
            }
            Self::Rewrite { target, rules } => Json::object(vec![
                tag("rw"),
                (
                    "at",
                    match target {
                        RewriteTarget::Goal => Json::Str("goal".to_owned()),
                        RewriteTarget::Hypothesis(local) => {
                            Json::from_usize(renumber.resolve(*local))
                        }
                    },
                ),
                (
                    "r",
                    Json::Arr(
                        rules
                            .iter()
                            .map(|rule| {
                                Json::object(vec![
                                    ("rev", Json::Bool(rule.reverse)),
                                    ("t", rule.term.to_json(renumber)),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
            Self::SimplifyOnly { target, rules } => Json::object(vec![
                tag("simp-only"),
                (
                    "at",
                    match target {
                        RewriteTarget::Goal => Json::Str("goal".to_owned()),
                        RewriteTarget::Hypothesis(local) => {
                            Json::from_usize(renumber.resolve(*local))
                        }
                    },
                ),
                (
                    "r",
                    Json::Arr(rules.iter().map(|rule| rule.to_json(renumber)).collect()),
                ),
            ]),
            Self::Constructor(branches) => Json::object(vec![
                tag("constructor"),
                (
                    "b",
                    Json::Arr(
                        branches
                            .iter()
                            .map(|branch| branch.to_json(renumber))
                            .collect(),
                    ),
                ),
            ]),
            Self::Cases { scrutinee, cases } | Self::Induction { scrutinee, cases } => {
                let name = if matches!(self, Self::Cases { .. }) {
                    "cases"
                } else {
                    "induction"
                };
                Json::object(vec![
                    tag(name),
                    ("t", scrutinee.to_json(renumber)),
                    (
                        "c",
                        Json::Arr(
                            cases
                                .iter()
                                .map(|case| {
                                    let binders: Vec<Json> = case
                                        .binders
                                        .iter()
                                        .map(|(local, _)| Json::from_usize(renumber.bind(*local)))
                                        .collect();
                                    Json::object(vec![
                                        ("ctor", Json::Str(case.constructor.to_string())),
                                        ("lean", Json::Str(case.lean_name.clone())),
                                        ("b", Json::Arr(binders)),
                                        ("p", case.proof.to_json(renumber)),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                ])
            }
            Self::Calculate {
                relation,
                start,
                steps,
            } => Json::object(vec![
                tag("calc"),
                (
                    "rel",
                    Term::Global(relation.clone(), Vec::new()).to_json(renumber),
                ),
                ("s", start.to_json(renumber)),
                (
                    "steps",
                    Json::Arr(
                        steps
                            .iter()
                            .map(|step| {
                                Json::object(vec![
                                    ("t", step.term.to_json(renumber)),
                                    ("p", step.proof.to_json(renumber)),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
        }
    }
}
