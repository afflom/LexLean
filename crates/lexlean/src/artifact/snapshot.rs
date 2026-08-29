//! Stable read-only semantic snapshot for LexLean projects (SPEC.md §24, Task 3).

use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::Sha256Digest;
use crate::link::CheckedProject;
use serde::{Deserialize, Serialize};

/// Stable semantic snapshot DTO.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticSnapshot {
    /// Schema spec identifier.
    pub spec: String,
    /// Source ID.
    pub source_id: Sha256Digest,
    /// Semantic ID.
    pub semantic_id: Sha256Digest,
    /// Compiler semantics ID.
    pub compiler_semantics_id: Sha256Digest,
    /// Language version (e.g. "1.0" or "1.1").
    pub language: String,
    /// Modules in the snapshot, sorted in canonical ASCII name order.
    pub modules: Vec<SnapshotModule>,
}

/// A module inside the semantic snapshot.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SnapshotModule {
    /// Module name.
    pub name: String,
    /// Generated Lean module name.
    pub lean_module: String,
    /// Declarations by component name, sorted canonically.
    pub declarations: Vec<SnapshotDeclaration>,
}

/// A declaration in a snapshot module.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SnapshotDeclaration {
    /// Component ID.
    pub id: String,
    /// Declaration kind (theorem, def, structure, class, instance, inductive).
    pub kind: String,
    /// Generated Lean name.
    pub lean_name: String,
    /// Axiom policy (none, allow, exact).
    pub axiom_policy: String,
}

impl SemanticSnapshot {
    /// Convert checked project into semantic snapshot.
    #[must_use]
    pub fn from_checked(checked: &CheckedProject, compiler_semantics_id: Sha256Digest) -> Self {
        let mut modules = Vec::new();
        for (name, module) in &checked.modules {
            let mut declarations = Vec::new();
            for decl in module.document.declarations() {
                declarations.push(SnapshotDeclaration {
                    id: decl.component.clone(),
                    kind: decl.kind.as_str().to_owned(),
                    lean_name: decl.lean_name.clone(),
                    axiom_policy: decl.policy.kind().to_owned(),
                });
            }
            declarations.sort_by(|a, b| a.id.cmp(&b.id));
            modules.push(SnapshotModule {
                name: name.clone(),
                lean_module: module.document.lean_module.clone(),
                declarations,
            });
        }
        modules.sort_by(|a, b| a.name.cmp(&b.name));

        Self {
            spec: "lexlean/semantic-snapshot/1".to_owned(),
            source_id: checked.source_id,
            semantic_id: checked.semantic_id,
            compiler_semantics_id,
            language: "1.1".to_owned(),
            modules,
        }
    }

    /// Canonical JSON representation of snapshot.
    #[must_use]
    pub fn to_json(&self) -> Json {
        let mut module_arr = Vec::new();
        for module in &self.modules {
            let mut decl_arr = Vec::new();
            for decl in &module.declarations {
                decl_arr.push(Json::object(vec![
                    ("axiom_policy", Json::Str(decl.axiom_policy.clone())),
                    ("id", Json::Str(decl.id.clone())),
                    ("kind", Json::Str(decl.kind.clone())),
                    ("lean_name", Json::Str(decl.lean_name.clone())),
                ]));
            }
            module_arr.push(Json::object(vec![
                ("declarations", Json::Arr(decl_arr)),
                ("lean_module", Json::Str(module.lean_module.clone())),
                ("name", Json::Str(module.name.clone())),
            ]));
        }

        Json::object(vec![
            (
                "compiler_semantics_id",
                Json::Str(self.compiler_semantics_id.to_hex()),
            ),
            ("language", Json::Str(self.language.clone())),
            ("modules", Json::Arr(module_arr)),
            ("semantic_id", Json::Str(self.semantic_id.to_hex())),
            ("source_id", Json::Str(self.source_id.to_hex())),
            ("spec", Json::Str(self.spec.clone())),
        ])
    }

    /// Canonical bytes.
    #[must_use]
    pub fn canonical_bytes(&self) -> Vec<u8> {
        self.to_json().to_file_bytes()
    }

    /// Snapshot content ID.
    #[must_use]
    pub fn snapshot_id(&self) -> Sha256Digest {
        Sha256Digest::of(&self.canonical_bytes())
    }
}
