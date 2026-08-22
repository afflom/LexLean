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
pub struct CoreStructureField {
    /// Source field name, normally a single name segment.
    pub name: String,
    /// Generated projection declaration.
    pub projection: String,
    /// Embedded parent structure for a subobject field.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub subobject: Option<String>,
    /// Original field binder visibility.
    pub binder: CoreBinderInfo,
    /// Deprecated Lean auto-parameter expression, retained losslessly when
    /// present in an imported environment.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub auto_param: Option<usize>,
}

/// One direct structure parent and its generated projection.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CoreStructureParent {
    /// Parent structure name.
    pub name: String,
    /// Whether the parent is represented by a stored subobject field.
    pub subobject: bool,
    /// Parent projection declaration.
    pub projection: String,
}

/// Elaborator metadata that distinguishes a structure from an ordinary
/// one-constructor inductive.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CoreStructure {
    /// Direct fields in constructor-field order.
    pub fields: Vec<CoreStructureField>,
    /// Direct parents in source order.
    pub parents: Vec<CoreStructureParent>,
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
    /// Exact structure registration metadata, absent for ordinary
    /// inductives.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub structure: Option<CoreStructure>,
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

/// Effective elaborator transparency attached to a declaration.  This is
/// distinct from the kernel definition hints above and is required for exact
/// downstream type-class and elaboration behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
pub enum CoreTransparency {
    #[serde(rename = "reducible")]
    Reducible,
    #[serde(rename = "semireducible")]
    Semireducible,
    #[serde(rename = "irreducible")]
    Irreducible,
    #[serde(rename = "implicit-reducible")]
    ImplicitReducible,
}

/// Scope behavior of a registered Lean attribute.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
pub enum CoreAttributeKind {
    #[serde(rename = "global")]
    Global,
    #[serde(rename = "local")]
    Local,
    #[serde(rename = "scoped")]
    Scoped,
}

/// Exact instance-extension metadata that is not part of the declaration's
/// kernel type or value.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CoreInstance {
    /// Type-class search priority.
    pub priority: u64,
    /// Attribute scope behavior.
    pub attribute: CoreAttributeKind,
    /// Argument synthesis order computed by the original elaborator.
    pub synthesis_order: Vec<usize>,
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
    /// Effective elaborator transparency.
    pub transparency: CoreTransparency,
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
    /// Instance-extension metadata, when registered as an instance.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub instance: Option<CoreInstance>,
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
        let module: Self = serde_json::from_str(text)
            .map_err(|error| format!("invalid core-module JSON: {error}"))?;
        module.validate()?;
        CanonicalSyntax::check(text.as_bytes())?;
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
                if let Some(structure) = &inductive.structure {
                    for field in &structure.fields {
                        validate_name(&field.name)?;
                        validate_name(&field.projection)?;
                        if let Some(subobject) = &field.subobject {
                            validate_name(subobject)?;
                        }
                        if field
                            .auto_param
                            .is_some_and(|node| node >= self.nodes.len())
                        {
                            return Err(format!(
                                "core structure `{}` has an out-of-range auto-parameter root",
                                declaration.name
                            ));
                        }
                    }
                    for parent in &structure.parents {
                        validate_name(&parent.name)?;
                        validate_name(&parent.projection)?;
                    }
                }
            }
        }
        Ok(())
    }
}

/// Streaming validation of the restricted canonical JSON spelling.  The
/// typed serde pass above owns schema validation; this pass enforces the
/// byte-level rules without allocating a second tree for a foundation model.
struct CanonicalSyntax<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> CanonicalSyntax<'a> {
    fn check(bytes: &'a [u8]) -> Result<(), String> {
        let mut parser = Self { bytes, at: 0 };
        parser.value()?;
        if parser.at != bytes.len() {
            return Err(
                "core-module JSON is not in canonical byte form: trailing bytes".to_owned(),
            );
        }
        Ok(())
    }

    fn current(&self) -> Option<u8> {
        self.bytes.get(self.at).copied()
    }

    fn take(&mut self, expected: u8) -> Result<(), String> {
        if self.current() != Some(expected) {
            return Err(format!(
                "core-module JSON is not in canonical byte form at byte {}",
                self.at
            ));
        }
        self.at += 1;
        Ok(())
    }

    fn literal(&mut self, value: &[u8]) -> Result<(), String> {
        if !self.bytes[self.at..].starts_with(value) {
            return Err(format!(
                "core-module JSON is not in canonical byte form at byte {}",
                self.at
            ));
        }
        self.at += value.len();
        Ok(())
    }

    fn value(&mut self) -> Result<(), String> {
        match self.current() {
            Some(b'{') => self.object(),
            Some(b'[') => self.array(),
            Some(b'"') => self.string(),
            Some(b't') => self.literal(b"true"),
            Some(b'f') => self.literal(b"false"),
            Some(b'-' | b'0'..=b'9') => self.integer(),
            _ => Err(format!(
                "core-module JSON is not in canonical byte form at byte {}",
                self.at
            )),
        }
    }

    fn object(&mut self) -> Result<(), String> {
        self.take(b'{')?;
        if self.current() == Some(b'}') {
            self.at += 1;
            return Ok(());
        }
        let mut previous: Option<String> = None;
        loop {
            let start = self.at;
            self.string()?;
            let key: String = serde_json::from_slice(&self.bytes[start..self.at])
                .map_err(|error| format!("invalid core-module JSON key: {error}"))?;
            if previous.as_ref().is_some_and(|prior| prior >= &key) {
                return Err(format!(
                    "core-module JSON is not in canonical byte form: object key `{key}` is not strictly ordered"
                ));
            }
            previous = Some(key);
            self.take(b':')?;
            self.value()?;
            match self.current() {
                Some(b',') => self.at += 1,
                Some(b'}') => {
                    self.at += 1;
                    return Ok(());
                }
                _ => {
                    return Err(format!(
                        "core-module JSON is not in canonical byte form at byte {}",
                        self.at
                    ));
                }
            }
        }
    }

    fn array(&mut self) -> Result<(), String> {
        self.take(b'[')?;
        if self.current() == Some(b']') {
            self.at += 1;
            return Ok(());
        }
        loop {
            self.value()?;
            match self.current() {
                Some(b',') => self.at += 1,
                Some(b']') => {
                    self.at += 1;
                    return Ok(());
                }
                _ => {
                    return Err(format!(
                        "core-module JSON is not in canonical byte form at byte {}",
                        self.at
                    ));
                }
            }
        }
    }

    fn string(&mut self) -> Result<(), String> {
        self.take(b'"')?;
        loop {
            match self.current() {
                Some(b'"') => {
                    self.at += 1;
                    return Ok(());
                }
                Some(b'\\') => {
                    self.at += 1;
                    match self.current() {
                        Some(b'"' | b'\\' | b'b' | b'f' | b'n' | b'r' | b't') => self.at += 1,
                        Some(b'u') => {
                            self.at += 1;
                            let end = self.at.checked_add(4).ok_or_else(|| {
                                "core-module JSON escape offset overflow".to_owned()
                            })?;
                            let Some(hex) = self.bytes.get(self.at..end) else {
                                return Err("unterminated core-module JSON escape".to_owned());
                            };
                            if !hex
                                .iter()
                                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
                            {
                                return Err("core-module JSON uses a noncanonical Unicode escape"
                                    .to_owned());
                            }
                            let value = hex.iter().fold(0u32, |value, byte| {
                                value * 16
                                    + u32::from(match byte {
                                        b'0'..=b'9' => byte - b'0',
                                        b'a'..=b'f' => byte - b'a' + 10,
                                        _ => 0,
                                    })
                            });
                            if value >= 0x20 || matches!(value, 0x08 | 0x09 | 0x0a | 0x0c | 0x0d) {
                                return Err(
                                    "core-module JSON uses a nonminimal Unicode escape".to_owned()
                                );
                            }
                            self.at = end;
                        }
                        _ => return Err("core-module JSON uses a noncanonical escape".to_owned()),
                    }
                }
                Some(0x00..=0x1f) => {
                    return Err("core-module JSON contains an unescaped control byte".to_owned());
                }
                Some(_) => self.at += 1,
                None => return Err("unterminated core-module JSON string".to_owned()),
            }
        }
    }

    fn integer(&mut self) -> Result<(), String> {
        let negative = self.current() == Some(b'-');
        if negative {
            self.at += 1;
        }
        match self.current() {
            Some(b'0') => {
                self.at += 1;
                if negative || self.current().is_some_and(|byte| byte.is_ascii_digit()) {
                    return Err("core-module JSON uses a noncanonical integer".to_owned());
                }
            }
            Some(b'1'..=b'9') => {
                self.at += 1;
                while self.current().is_some_and(|byte| byte.is_ascii_digit()) {
                    self.at += 1;
                }
            }
            _ => return Err("core-module JSON contains an invalid integer".to_owned()),
        }
        if self
            .current()
            .is_some_and(|byte| matches!(byte, b'.' | b'e' | b'E' | b'+'))
        {
            return Err("core-module JSON contains a non-integer number".to_owned());
        }
        Ok(())
    }
}

#[cfg(test)]
mod canonical_syntax_tests {
    use super::CanonicalSyntax;

    #[test]
    fn canonical_json_is_checked_without_a_value_tree() {
        assert!(CanonicalSyntax::check(br#"{"a":[0,true,"x\n"],"b":-2}"#).is_ok());
        for rejected in [
            br#"{"b":0,"a":0}"#.as_slice(),
            br#"{"a": 0}"#.as_slice(),
            br#"{"a":"\u0061"}"#.as_slice(),
            br#"{"a":-0}"#.as_slice(),
            br#"{"a":null}"#.as_slice(),
        ] {
            assert!(CanonicalSyntax::check(rejected).is_err());
        }
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
