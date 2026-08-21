//! Closed kernel-term IR used for lossless migrations of already elaborated
//! formal libraries.  The representation is a DAG: every edge points to an
//! earlier node, so decoding is bounded, cycle-free, and traversable by both
//! backends.  It is semantic data, never backend source text.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

/// A universe level in the kernel calculus.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "k", content = "a")]
#[serde(deny_unknown_fields)]
pub enum CoreLevel {
    /// Level zero.
    #[serde(rename = "z")]
    Zero,
    /// Successor.
    #[serde(rename = "s")]
    Succ(Box<CoreLevel>),
    /// Maximum.
    #[serde(rename = "m")]
    Max(Box<(CoreLevel, CoreLevel)>),
    /// Impredicative maximum.
    #[serde(rename = "i")]
    IMax(Box<(CoreLevel, CoreLevel)>),
    /// A declaration universe parameter.
    #[serde(rename = "p")]
    Param(String),
}

/// Binder visibility, preserved from the elaborated kernel expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
pub enum CoreBinderInfo {
    /// Ordinary explicit binder.
    #[serde(rename = "e")]
    Explicit,
    /// Implicit binder.
    #[serde(rename = "i")]
    Implicit,
    /// Strict implicit binder.
    #[serde(rename = "s")]
    StrictImplicit,
    /// Type-class instance binder.
    #[serde(rename = "c")]
    Instance,
}

/// One node of a closed Calculus-of-Inductive-Constructions expression.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "k")]
#[serde(deny_unknown_fields)]
pub enum CoreNode {
    /// De Bruijn variable.
    #[serde(rename = "b")]
    BVar { i: usize },
    /// Sort.
    #[serde(rename = "s")]
    Sort { l: CoreLevel },
    /// Universe-instantiated global constant.
    #[serde(rename = "c")]
    Const { n: String, u: Vec<CoreLevel> },
    /// Application.
    #[serde(rename = "a")]
    App { f: usize, x: usize },
    /// Lambda.
    #[serde(rename = "l")]
    Lambda {
        n: String,
        b: CoreBinderInfo,
        t: usize,
        v: usize,
    },
    /// Dependent function type.
    #[serde(rename = "p")]
    Forall {
        n: String,
        b: CoreBinderInfo,
        t: usize,
        v: usize,
    },
    /// Let expression.
    #[serde(rename = "e")]
    Let {
        n: String,
        t: usize,
        v: usize,
        body: usize,
        d: bool,
    },
    /// Natural-number literal.
    #[serde(rename = "n")]
    Nat { v: String },
    /// String literal, encoded as Unicode scalar values so source whitespace
    /// and TeX metacharacters never acquire a second interpretation.
    #[serde(rename = "t")]
    String { v: Vec<u32> },
    /// Primitive structure projection.
    #[serde(rename = "j")]
    Projection {
        /// Projection function name, used by the readable renderers.
        n: String,
        /// Structure type name used by the kernel projection node.
        s: String,
        /// Zero-based projection index.
        i: usize,
        x: usize,
    },
}

impl CoreNode {
    fn children(&self) -> Vec<usize> {
        match self {
            Self::App { f, x } => vec![*f, *x],
            Self::Lambda { t, v, .. } | Self::Forall { t, v, .. } => vec![*t, *v],
            Self::Let { t, v, body, .. } => vec![*t, *v, *body],
            Self::Projection { x, .. } => vec![*x],
            Self::BVar { .. }
            | Self::Sort { .. }
            | Self::Const { .. }
            | Self::Nat { .. }
            | Self::String { .. } => Vec::new(),
        }
    }
}

/// Inductive metadata needed to reproduce the kernel declaration.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CoreInductive {
    /// Fixed parameters.
    pub num_params: usize,
    /// Varying indices.
    pub num_indices: usize,
    /// Constructor declaration names, in kernel order.
    pub constructors: Vec<String>,
    /// Whether the old elaborator registered this inductive as a structure.
    pub structure: bool,
    /// Direct projection names in constructor-field order for a structure.
    #[serde(default)]
    pub projections: Vec<String>,
}

/// How a declaration participates in generated Lean.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
pub enum CoreDeclKind {
    /// Reducible abbreviation.
    #[serde(rename = "abbrev")]
    Abbrev,
    /// Definition.
    #[serde(rename = "definition")]
    Definition,
    /// Proof-bearing theorem.
    #[serde(rename = "theorem")]
    Theorem,
    /// Inductive or structure type former.
    #[serde(rename = "inductive")]
    Inductive,
    /// Constructor generated with its inductive.
    #[serde(rename = "constructor")]
    Constructor,
    /// Recursor generated with its inductive.
    #[serde(rename = "recursor")]
    Recursor,
}

/// Kernel reducibility metadata for a definition.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "kind", content = "height")]
#[serde(deny_unknown_fields)]
pub enum CoreReducibility {
    /// An abbreviation is unfolded before ordinary definitions.
    #[serde(rename = "abbrev")]
    Abbrev,
    /// An ordinary definition whose kernel unfolding hint is opaque.
    #[serde(rename = "opaque")]
    Opaque,
    /// An ordinary definition with its exact dependency height.
    #[serde(rename = "regular")]
    Regular(u32),
}

/// An explicit axiom policy for a native core declaration.  Core modules do
/// not inherit a module-wide default: generated and directly submitted
/// declarations alike carry the policy that verification enforces.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "kind", content = "axioms")]
#[serde(deny_unknown_fields)]
pub enum CoreAxiomPolicy {
    /// The observed axiom set must be empty.
    #[serde(rename = "none")]
    None,
    /// The observed set must be a subset of this list.
    #[serde(rename = "allow")]
    Allow(Vec<String>),
    /// The observed set must equal this list.
    #[serde(rename = "exact")]
    Exact(Vec<String>),
}

impl CoreAxiomPolicy {
    /// The policy kind used in verification records and diagnostics.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Allow(_) => "allow",
            Self::Exact(_) => "exact",
        }
    }

    /// The configured axiom names.
    #[must_use]
    pub fn axioms(&self) -> &[String] {
        match self {
            Self::None => &[],
            Self::Allow(names) | Self::Exact(names) => names,
        }
    }

    /// Enforce the policy against the normalized observed set.
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

/// One declaration linked to exact type and, where applicable, value nodes.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CoreDeclaration {
    /// Generated global name.
    pub name: String,
    /// Universe parameters in declaration order.
    pub levels: Vec<String>,
    /// Declaration kind.
    pub kind: CoreDeclKind,
    /// Exact kernel reducibility metadata for definitions and abbreviations.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reducibility: Option<CoreReducibility>,
    /// Explicit per-declaration axiom policy.
    pub policy: CoreAxiomPolicy,
    /// Type root.
    pub r#type: usize,
    /// Value/proof root for definitions and theorems.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value: Option<usize>,
    /// Inductive metadata exactly for inductive declarations.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub inductive: Option<CoreInductive>,
    /// Whether this type is a type class.
    #[serde(default)]
    pub class: bool,
    /// Whether this declaration is an instance.
    #[serde(default)]
    pub instance: bool,
    /// Instance priority when `instance` is true.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub priority: Option<u64>,
    /// Whether the matching inductive/structure command creates this
    /// declaration.  Such rows remain in the IR and audit, but are not emitted
    /// twice.
    #[serde(default)]
    pub generated: bool,
}

/// A complete native core module.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CoreModule {
    /// Schema discriminator.
    pub spec: String,
    /// Lean modules containing the foundational constants referenced by the
    /// DAG.  Generated declarations themselves never appear here.
    pub imports: Vec<String>,
    /// Shared expression DAG in child-before-parent order.
    pub nodes: Vec<CoreNode>,
    /// Closed proof nodes.  They remain inline so dependent expected types are
    /// preserved instead of being weakened to a globally inferred helper
    /// type.
    #[serde(default)]
    pub proof_nodes: Vec<usize>,
    /// Declaration rows in dependency order.
    pub declarations: Vec<CoreDeclaration>,
}

impl CoreModule {
    /// Decode and enforce the closed schema invariants.
    pub fn parse(text: &str) -> Result<Self, String> {
        let value: serde_json::Value = serde_json::from_str(text)
            .map_err(|error| format!("invalid core-module JSON: {error}"))?;
        let module: Self = serde_json::from_value(value)
            .map_err(|error| format!("invalid core-module JSON: {error}"))?;
        module.validate()?;
        let canonical = serde_json::to_string(
            &serde_json::to_value(&module)
                .map_err(|error| format!("cannot canonicalize core-module JSON: {error}"))?,
        )
        .map_err(|error| format!("cannot canonicalize core-module JSON: {error}"))?;
        if text != canonical {
            return Err("core-module JSON is not in canonical byte form".to_owned());
        }
        Ok(module)
    }

    fn validate(&self) -> Result<(), String> {
        if self.spec != "lexlean/core-module/1" {
            return Err(format!("unsupported core-module schema `{}`", self.spec));
        }
        if self.declarations.is_empty() {
            return Err("a core module contains at least one declaration".to_owned());
        }
        let mut imports = BTreeSet::new();
        for import in &self.imports {
            validate_name(import)?;
            if !imports.insert(import) {
                return Err(format!("duplicate core import `{import}`"));
            }
        }
        for (index, node) in self.nodes.iter().enumerate() {
            for child in node.children() {
                if child >= index {
                    return Err(format!(
                        "core node {index} points to non-earlier node {child}"
                    ));
                }
            }
            match node {
                CoreNode::Const { n, .. } => validate_name(n)?,
                CoreNode::Projection { n, s, .. } => {
                    validate_name(n)?;
                    validate_name(s)?;
                }
                CoreNode::BVar { .. }
                | CoreNode::Sort { .. }
                | CoreNode::App { .. }
                | CoreNode::Lambda { .. }
                | CoreNode::Forall { .. }
                | CoreNode::Let { .. }
                | CoreNode::Nat { .. }
                | CoreNode::String { .. } => {}
            }
        }
        let mut previous = None;
        for proof in &self.proof_nodes {
            if *proof >= self.nodes.len() {
                return Err(format!("core proof node {proof} is out of range"));
            }
            if previous.is_some_and(|prior| prior >= *proof) {
                return Err("core proof nodes are strictly increasing".to_owned());
            }
            previous = Some(*proof);
        }
        let mut names = BTreeSet::new();
        for declaration in &self.declarations {
            validate_name(&declaration.name)?;
            if !names.insert(&declaration.name) {
                return Err(format!("duplicate core declaration `{}`", declaration.name));
            }
            if declaration.r#type >= self.nodes.len()
                || declaration
                    .value
                    .is_some_and(|value| value >= self.nodes.len())
            {
                return Err(format!(
                    "core declaration `{}` has an out-of-range expression root",
                    declaration.name
                ));
            }
            let has_value = declaration.value.is_some();
            if matches!(
                declaration.kind,
                CoreDeclKind::Abbrev | CoreDeclKind::Definition | CoreDeclKind::Theorem
            ) != has_value
            {
                return Err(format!(
                    "core declaration `{}` has a kind/value mismatch",
                    declaration.name
                ));
            }
            if matches!(declaration.kind, CoreDeclKind::Inductive)
                != declaration.inductive.is_some()
            {
                return Err(format!(
                    "core declaration `{}` has a kind/inductive mismatch",
                    declaration.name
                ));
            }
            if matches!(
                declaration.kind,
                CoreDeclKind::Definition | CoreDeclKind::Abbrev
            ) != declaration.reducibility.is_some()
            {
                return Err(format!(
                    "core declaration `{}` has a kind/reducibility-metadata mismatch",
                    declaration.name
                ));
            }
            if matches!(declaration.kind, CoreDeclKind::Abbrev)
                != matches!(declaration.reducibility, Some(CoreReducibility::Abbrev))
            {
                return Err(format!(
                    "core declaration `{}` has an inconsistent abbreviation hint",
                    declaration.name
                ));
            }
            if declaration.instance != declaration.priority.is_some() {
                return Err(format!(
                    "core declaration `{}` has an inconsistent instance priority",
                    declaration.name
                ));
            }
            let mut policy_names = BTreeSet::new();
            for axiom in declaration.policy.axioms() {
                validate_name(axiom)?;
                if !policy_names.insert(axiom) {
                    return Err(format!(
                        "core declaration `{}` repeats axiom `{axiom}` in its policy",
                        declaration.name
                    ));
                }
            }
            for level in &declaration.levels {
                validate_segment(level)?;
            }
            if let Some(inductive) = &declaration.inductive {
                if inductive.constructors.is_empty() {
                    return Err(format!(
                        "core inductive `{}` has no constructors",
                        declaration.name
                    ));
                }
                for name in &inductive.constructors {
                    validate_name(name)?;
                    if !names.contains(name)
                        && !self.declarations.iter().any(|row| row.name == *name)
                    {
                        return Err(format!(
                            "core inductive `{}` names absent constructor `{name}`",
                            declaration.name
                        ));
                    }
                }
                for projection in &inductive.projections {
                    validate_name(projection)?;
                }
                if !inductive.structure && !inductive.projections.is_empty() {
                    return Err(format!(
                        "non-structure `{}` carries projection metadata",
                        declaration.name
                    ));
                }
            }
        }
        Ok(())
    }

    /// Canonical semantic JSON included in the linked-IR identity.
    #[must_use]
    pub fn semantic_json(&self) -> serde_json::Value {
        serde_json::to_value(self).unwrap_or(serde_json::Value::Null)
    }
}

fn validate_segment(segment: &str) -> Result<(), String> {
    let mut chars = segment.chars();
    let Some(first) = chars.next() else {
        return Err("empty Lean name segment".to_owned());
    };
    if !(first.is_ascii_alphabetic() || first == '_')
        || !chars.all(|character| character.is_ascii_alphanumeric() || "_?'".contains(character))
    {
        return Err(format!(
            "`{segment}` is not a closed ASCII Lean name segment"
        ));
    }
    Ok(())
}

fn validate_name(name: &str) -> Result<(), String> {
    if name.is_empty() {
        return Err("empty Lean name".to_owned());
    }
    for segment in name.split('.') {
        validate_segment(segment)?;
    }
    Ok(())
}
