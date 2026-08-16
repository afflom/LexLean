//! Declaration IR (SPEC.md §17.5, §15.7–§15.9).

use crate::artifact::canonical_json::Json;
use crate::ir::proof::Proof;
use crate::ir::term::{Binder, Renumber, Term};
use crate::lexicon::lse::QualifiedId;

/// The declaration kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclKind {
    /// `typedefinition`.
    TypeDefinition,
    /// `termdefinition`.
    TermDefinition,
    /// `predicatedefinition`.
    PredicateDefinition,
    /// `theorem`.
    Theorem,
    /// `lemma`.
    Lemma,
    /// `corollary`.
    Corollary,
}

impl DeclKind {
    /// Is this a theorem-like kind (§15.8)?
    #[must_use]
    pub const fn is_theorem_like(self) -> bool {
        matches!(self, Self::Theorem | Self::Lemma | Self::Corollary)
    }

    /// The stable serialization tag, also the source environment name.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TypeDefinition => "typedefinition",
            Self::TermDefinition => "termdefinition",
            Self::PredicateDefinition => "predicatedefinition",
            Self::Theorem => "theorem",
            Self::Lemma => "lemma",
            Self::Corollary => "corollary",
        }
    }
}

/// An explicit axiom policy (§15.9). There is no inherited module policy
/// and no implicit default.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AxiomPolicy {
    /// `\noaxioms`: the observed set must be empty.
    None,
    /// `\allowaxioms{...}`: the observed set must be a subset.
    Allow(Vec<String>),
    /// `\exactaxioms{...}`: the observed set must be equal.
    Exact(Vec<String>),
}

impl AxiomPolicy {
    /// The policy kind token.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Allow(_) => "allow",
            Self::Exact(_) => "exact",
        }
    }

    /// The configured name list.
    #[must_use]
    pub fn axioms(&self) -> &[String] {
        match self {
            Self::None => &[],
            Self::Allow(names) | Self::Exact(names) => names,
        }
    }

    /// Enforce the policy against an observed set (§22.6).
    #[must_use]
    pub fn permits(&self, observed: &[String]) -> bool {
        match self {
            Self::None => observed.is_empty(),
            Self::Allow(allowed) => observed.iter().all(|axiom| allowed.contains(axiom)),
            Self::Exact(exact) => {
                let mut sorted = observed.to_vec();
                sorted.sort();
                sorted.dedup();
                sorted == *exact
            }
        }
    }
}

/// The body of a declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclBody {
    /// A type, term, or predicate definition (§15.7).
    Definition {
        /// The document entry this definition realizes.
        entry: QualifiedId,
        /// The explicit generated type.
        ty: Term,
        /// The generated value.
        value: Term,
    },
    /// A theorem-like statement with its proof (§15.8).
    TheoremLike {
        /// The full proposition, leading universals included.
        statement: Term,
        /// The structured proof.
        proof: Proof,
    },
}

/// One linked declaration (§17.5).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declaration {
    /// The source component ID.
    pub component: String,
    /// The generated short Lean name (component with `-` changed to `_`).
    pub lean_name: String,
    /// The kind.
    pub kind: DeclKind,
    /// Inherited section parameters this declaration uses, in scope order.
    pub params: Vec<Binder>,
    /// The body.
    pub body: DeclBody,
    /// The explicit axiom policy.
    pub policy: AxiomPolicy,
}

impl Declaration {
    /// Canonical, alpha-safe JSON (§17.9).
    #[must_use]
    pub fn to_json(&self, renumber: &mut Renumber) -> Json {
        let params: Vec<Json> = self
            .params
            .iter()
            .map(|binder| {
                let ty = binder.ty.to_json(renumber);
                let index = renumber.bind(binder.id);
                Json::object(vec![
                    ("id", Json::from_usize(index)),
                    ("m", Json::Str(binder.mode.as_str().to_owned())),
                    ("s", Json::Str(binder.spelling.clone())),
                    ("t", ty),
                ])
            })
            .collect();
        let body = match &self.body {
            DeclBody::Definition { entry, ty, value } => Json::object(vec![
                ("k", Json::Str("definition".to_owned())),
                ("entry", Json::Str(entry.to_string())),
                ("t", ty.to_json(renumber)),
                ("v", value.to_json(renumber)),
            ]),
            DeclBody::TheoremLike { statement, proof } => Json::object(vec![
                ("k", Json::Str("theorem".to_owned())),
                ("s", statement.to_json(renumber)),
                ("p", proof.to_json(renumber)),
            ]),
        };
        Json::object(vec![
            ("component", Json::Str(self.component.clone())),
            ("lean_name", Json::Str(self.lean_name.clone())),
            ("kind", Json::Str(self.kind.as_str().to_owned())),
            ("params", Json::Arr(params)),
            ("body", body),
            (
                "policy",
                Json::object(vec![
                    ("kind", Json::Str(self.policy.kind().to_owned())),
                    (
                        "axioms",
                        Json::Arr(
                            self.policy
                                .axioms()
                                .iter()
                                .cloned()
                                .map(Json::Str)
                                .collect(),
                        ),
                    ),
                ]),
            ),
        ])
    }
}
