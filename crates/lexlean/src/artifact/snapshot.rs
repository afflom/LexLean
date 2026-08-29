//! Stable, owned semantic snapshot DTOs.
//!
//! The snapshot contains canonical linked semantic data, never Rust debug
//! output and never a reference to LexLean's mutable compiler structures.

use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::Sha256Digest;
use crate::ir::core::CoreDeclKind;
use crate::ir::semantic::SemanticModule;
use crate::ir::term::Renumber;
use crate::link::CheckedProject;
use serde::{Deserialize, Serialize};

/// Stable semantic snapshot envelope (`lexlean/semantic-snapshot/1`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticSnapshot {
    spec: String,
    source_id: Sha256Digest,
    semantic_id: Sha256Digest,
    compiler_semantics_id: Sha256Digest,
    language: String,
    modules: Vec<SnapshotModule>,
    lexicon_closure: serde_json::Value,
}

/// One linked module in canonical module-name order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SnapshotModule {
    name: String,
    lean_module: String,
    imports: Vec<String>,
    glossary: Vec<String>,
    visible_packages: Vec<String>,
    source: SnapshotSource,
    declarations: Vec<SnapshotDeclaration>,
    /// Native semantic declarations, expression DAG, structure/class,
    /// instance, inductive, recursion, and proof metadata.  This is nested
    /// JSON, never an encoded JSON string.
    #[serde(skip_serializing_if = "Option::is_none")]
    core: Option<serde_json::Value>,
    /// High-level declaration/term/proof data for a language-1.1 semantic
    /// module.
    #[serde(skip_serializing_if = "Option::is_none")]
    semantic: Option<SemanticModule>,
    linked_ir: serde_json::Value,
}

/// Normalized source identity. Absolute checkout paths are never represented.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SnapshotSource {
    path: String,
    sha256: Sha256Digest,
}

/// One source byte range `[start, end)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SnapshotRange {
    start: usize,
    end: usize,
}

/// Normalized source origins for a declaration and its proof steps.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SnapshotOrigin {
    whole: SnapshotRange,
    sentence: SnapshotRange,
    #[serde(skip_serializing_if = "Option::is_none")]
    proof: Option<SnapshotRange>,
    proof_steps: Vec<SnapshotRange>,
}

/// One stable linked declaration row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SnapshotDeclaration {
    logical_id: String,
    kind: String,
    lean_name: String,
    axiom_policy: SnapshotAxiomPolicy,
    #[serde(skip_serializing_if = "Option::is_none")]
    origin: Option<SnapshotOrigin>,
    /// The closed canonical semantic value containing binders, qualified
    /// references, terms, proofs, recursion, fields, constructors and
    /// instance metadata as applicable to the declaration kind.
    linked_ir: serde_json::Value,
}

/// Closed declaration axiom policy.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SnapshotAxiomPolicy {
    kind: String,
    axioms: Vec<String>,
}

fn range((start, end): (usize, usize)) -> SnapshotRange {
    SnapshotRange { start, end }
}

fn json_value(value: &Json) -> serde_json::Value {
    serde_json::from_str(&value.to_canonical_string()).expect("canonical linked IR is valid JSON")
}

fn core_kind(kind: CoreDeclKind, class: bool, instance: bool) -> &'static str {
    if instance {
        "instance"
    } else if class {
        "class"
    } else {
        match kind {
            CoreDeclKind::Abbrev => "abbrev",
            CoreDeclKind::Definition => "definition",
            CoreDeclKind::Theorem => "theorem",
            CoreDeclKind::Inductive => "inductive",
            CoreDeclKind::Constructor => "constructor",
            CoreDeclKind::Recursor => "recursor",
        }
    }
}

impl SemanticSnapshot {
    /// Convert checked semantic data into the stable snapshot. Hidden compiler
    /// types cannot enter the public API because this constructor is private
    /// to the crate.
    pub(crate) fn from_checked(
        checked: &CheckedProject,
        language: &str,
        compiler_semantics_id: Sha256Digest,
    ) -> Self {
        let mut modules = Vec::with_capacity(checked.modules.len());
        for (name, module) in &checked.modules {
            let mut declarations = Vec::new();
            for declaration in module.document.declarations() {
                let origin = module
                    .decl_origins
                    .get(&declaration.component)
                    .map(|origin| SnapshotOrigin {
                        whole: range(origin.whole),
                        sentence: range(origin.sentence),
                        proof: origin.proof.map(range),
                        proof_steps: origin.steps.iter().copied().map(range).collect(),
                    });
                declarations.push(SnapshotDeclaration {
                    logical_id: declaration.component.clone(),
                    kind: declaration.kind.as_str().to_owned(),
                    lean_name: declaration.lean_name.clone(),
                    axiom_policy: SnapshotAxiomPolicy {
                        kind: declaration.policy.kind().to_owned(),
                        axioms: declaration.policy.axioms().to_vec(),
                    },
                    origin,
                    linked_ir: json_value(&declaration.to_json(&mut Renumber::default())),
                });
            }
            if let Some(core) = &module.document.core {
                for declaration in &core.declarations {
                    declarations.push(SnapshotDeclaration {
                        logical_id: declaration.name.clone(),
                        kind: core_kind(
                            declaration.kind,
                            declaration.class,
                            declaration.instance.is_some(),
                        )
                        .to_owned(),
                        lean_name: declaration.name.clone(),
                        axiom_policy: SnapshotAxiomPolicy {
                            kind: declaration.policy.kind().to_owned(),
                            axioms: declaration.policy.axioms().to_vec(),
                        },
                        origin: None,
                        linked_ir: serde_json::to_value(declaration)
                            .expect("core declarations serialize"),
                    });
                }
            }
            if let Some(semantic) = &module.document.semantic {
                for declaration in &semantic.declarations {
                    declarations.push(SnapshotDeclaration {
                        logical_id: declaration.name().to_owned(),
                        kind: declaration.kind().to_owned(),
                        lean_name: declaration.name().to_owned(),
                        axiom_policy: SnapshotAxiomPolicy {
                            kind: declaration.axiom_policy_kind().to_owned(),
                            axioms: declaration.axioms().to_vec(),
                        },
                        origin: None,
                        linked_ir: serde_json::to_value(declaration)
                            .expect("semantic declaration serializes"),
                    });
                }
            }
            declarations
                .sort_by(|left, right| left.logical_id.as_bytes().cmp(right.logical_id.as_bytes()));
            modules.push(SnapshotModule {
                name: name.clone(),
                lean_module: module.document.lean_module.clone(),
                imports: module.document.imports.clone(),
                glossary: module.document.glossary.clone(),
                visible_packages: module.visible.iter().cloned().collect(),
                source: SnapshotSource {
                    path: module.document.source_path.clone(),
                    sha256: module.document.source_sha256,
                },
                declarations,
                core: module
                    .document
                    .core
                    .as_ref()
                    .map(|core| serde_json::to_value(core).expect("core module serializes")),
                semantic: module.document.semantic.clone(),
                linked_ir: json_value(&module.document.to_json()),
            });
        }
        modules.sort_by(|left, right| left.name.as_bytes().cmp(right.name.as_bytes()));
        let closure = checked.closure.closure_json("", &checked.visible_union);
        Self {
            spec: "lexlean/semantic-snapshot/1".to_owned(),
            source_id: checked.source_id,
            semantic_id: checked.semantic_id,
            compiler_semantics_id,
            language: language.to_owned(),
            modules,
            lexicon_closure: json_value(&closure),
        }
    }

    /// Schema identifier.
    #[must_use]
    pub fn spec(&self) -> &str {
        &self.spec
    }

    /// Source identity.
    #[must_use]
    pub const fn source_id(&self) -> Sha256Digest {
        self.source_id
    }

    /// Semantic identity.
    #[must_use]
    pub const fn semantic_id(&self) -> Sha256Digest {
        self.semantic_id
    }

    /// Compiler-semantics identity.
    #[must_use]
    pub const fn compiler_semantics_id(&self) -> Sha256Digest {
        self.compiler_semantics_id
    }

    /// Selected language version.
    #[must_use]
    pub fn language(&self) -> &str {
        &self.language
    }

    /// Canonically ordered modules.
    #[must_use]
    pub fn modules(&self) -> &[SnapshotModule] {
        &self.modules
    }

    /// Complete locked lexicon/package closure in canonical order.
    #[must_use]
    pub const fn lexicon_closure(&self) -> &serde_json::Value {
        &self.lexicon_closure
    }

    /// Canonical JSON value.
    #[must_use]
    pub fn to_json(&self) -> Json {
        let value = serde_json::to_value(self).expect("snapshot DTO serializes");
        let bytes = serde_json::to_vec(&value).expect("snapshot JSON serializes");
        Json::parse(&bytes).expect("snapshot DTO uses the canonical JSON domain")
    }

    /// Canonical JSON file bytes, including LexLean's single final LF.
    #[must_use]
    pub fn canonical_bytes(&self) -> Vec<u8> {
        self.to_json().to_file_bytes()
    }

    /// SHA-256 of [`Self::canonical_bytes`].
    #[must_use]
    pub fn snapshot_id(&self) -> Sha256Digest {
        Sha256Digest::of(&self.canonical_bytes())
    }
}

impl SnapshotModule {
    /// Logical module name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Generated Lean module name.
    #[must_use]
    pub fn lean_module(&self) -> &str {
        &self.lean_module
    }

    /// Canonically ordered declarations.
    #[must_use]
    pub fn declarations(&self) -> &[SnapshotDeclaration] {
        &self.declarations
    }

    /// Explicit source-module imports.
    #[must_use]
    pub fn imports(&self) -> &[String] {
        &self.imports
    }

    /// Explicit glossary-package closure at the module boundary.
    #[must_use]
    pub fn glossary(&self) -> &[String] {
        &self.glossary
    }

    /// Complete visible package closure in canonical order.
    #[must_use]
    pub fn visible_packages(&self) -> &[String] {
        &self.visible_packages
    }

    /// Normalized project-relative source identity.
    #[must_use]
    pub const fn source(&self) -> &SnapshotSource {
        &self.source
    }

    /// Native semantic module data, when this source uses the closed core
    /// declaration language.
    #[must_use]
    pub fn core(&self) -> Option<&serde_json::Value> {
        self.core.as_ref()
    }

    /// High-level declaration, term, recursion, and proof data.
    #[must_use]
    pub const fn semantic(&self) -> Option<&SemanticModule> {
        self.semantic.as_ref()
    }

    /// Complete canonical linked module IR.
    #[must_use]
    pub const fn linked_ir(&self) -> &serde_json::Value {
        &self.linked_ir
    }
}

impl SnapshotDeclaration {
    /// Stable logical component ID or full native-core declaration name.
    #[must_use]
    pub fn logical_id(&self) -> &str {
        &self.logical_id
    }

    /// Stable declaration-kind tag.
    #[must_use]
    pub fn kind(&self) -> &str {
        &self.kind
    }

    /// Generated Lean declaration name.
    #[must_use]
    pub fn lean_name(&self) -> &str {
        &self.lean_name
    }

    /// Closed linked semantic value for this declaration.
    #[must_use]
    pub fn linked_ir(&self) -> &serde_json::Value {
        &self.linked_ir
    }

    /// Normalized source origin, when the declaration was written through
    /// the prose declaration language.
    #[must_use]
    pub const fn origin(&self) -> Option<&SnapshotOrigin> {
        self.origin.as_ref()
    }

    /// Closed axiom policy enforced by verification.
    #[must_use]
    pub const fn axiom_policy(&self) -> &SnapshotAxiomPolicy {
        &self.axiom_policy
    }
}

impl SnapshotSource {
    /// Project-relative normalized source path.
    #[must_use]
    pub fn path(&self) -> &str {
        &self.path
    }

    /// Hash of the normalized source bytes.
    #[must_use]
    pub const fn sha256(&self) -> Sha256Digest {
        self.sha256
    }
}

impl SnapshotAxiomPolicy {
    /// Policy discriminator: `none`, `allow`, or `exact`.
    #[must_use]
    pub fn kind(&self) -> &str {
        &self.kind
    }

    /// Canonically ordered permitted/required axiom names.
    #[must_use]
    pub fn axioms(&self) -> &[String] {
        &self.axioms
    }
}
