//! Build manifests (SPEC.md §21.6).

use std::collections::BTreeMap;

use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::Sha256Digest;

/// One input or output row: kind, stable `/`-separated path, size, hash.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FileRow {
    /// The row kind, e.g. `lean`, `tex`, `map`, `coverage`,
    /// `lexicon-closure`, `source`, `project-config`, `lock`.
    pub kind: String,
    /// Project- or build-relative path with `/` separators on every host.
    pub path: String,
    /// Exact byte length.
    pub byte_length: usize,
    /// SHA-256 of the bytes.
    pub sha256: Sha256Digest,
}

impl FileRow {
    fn to_json(&self) -> Json {
        Json::object(vec![
            ("kind", Json::Str(self.kind.clone())),
            ("path", Json::Str(self.path.clone())),
            ("byte_length", Json::from_usize(self.byte_length)),
            ("sha256", Json::Str(self.sha256.to_hex())),
        ])
    }
}

/// One module row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleRow {
    /// The source module name, e.g. `Main`.
    pub module: String,
    /// The full generated Lean module name.
    pub lean_module: String,
    /// The project-relative source path.
    pub source_path: String,
}

/// The build manifest (§21.6). It never contains its own hash.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildManifest {
    /// Compiler crate version.
    pub compiler_version: String,
    /// The embedded compiler-semantics ID.
    pub semantics_id: Sha256Digest,
    /// The project name.
    pub project: String,
    /// The source ID.
    pub source_id: Sha256Digest,
    /// The semantic ID.
    pub semantic_id: Sha256Digest,
    /// The build ID.
    pub build_id: Sha256Digest,
    /// Selected module names, sorted.
    pub selection: Vec<String>,
    /// Module rows in sorted module order.
    pub modules: Vec<ModuleRow>,
    /// Input rows, sorted by `(kind, path)`.
    pub inputs: Vec<FileRow>,
    /// Output rows, sorted by `(kind, path)`.
    pub outputs: Vec<FileRow>,
}

impl BuildManifest {
    /// The canonical JSON object; rows are sorted here so callers cannot
    /// publish an unsorted manifest.
    #[must_use]
    pub fn to_json(&self) -> Json {
        let mut inputs = self.inputs.clone();
        inputs.sort();
        let mut outputs = self.outputs.clone();
        outputs.sort();
        let mut o = BTreeMap::new();
        o.insert(
            "spec".to_owned(),
            Json::Str("lexlean/build-manifest/1".to_owned()),
        );
        o.insert(
            "compiler".to_owned(),
            Json::object(vec![
                ("version", Json::Str(self.compiler_version.clone())),
                ("semantics_id", Json::Str(self.semantics_id.to_hex())),
            ]),
        );
        o.insert(
            "language".to_owned(),
            Json::Str(crate::LANGUAGE_VERSION.to_owned()),
        );
        o.insert("project".to_owned(), Json::Str(self.project.clone()));
        o.insert("source_id".to_owned(), Json::Str(self.source_id.to_hex()));
        o.insert(
            "semantic_id".to_owned(),
            Json::Str(self.semantic_id.to_hex()),
        );
        o.insert("build_id".to_owned(), Json::Str(self.build_id.to_hex()));
        o.insert(
            "lean_toolchain".to_owned(),
            Json::Str(crate::LEAN_TOOLCHAIN.to_owned()),
        );
        o.insert(
            "selection".to_owned(),
            Json::Arr(self.selection.iter().cloned().map(Json::Str).collect()),
        );
        o.insert(
            "modules".to_owned(),
            Json::Arr(
                self.modules
                    .iter()
                    .map(|row| {
                        Json::object(vec![
                            ("module", Json::Str(row.module.clone())),
                            ("lean_module", Json::Str(row.lean_module.clone())),
                            ("source_path", Json::Str(row.source_path.clone())),
                        ])
                    })
                    .collect(),
            ),
        );
        o.insert(
            "inputs".to_owned(),
            Json::Arr(inputs.iter().map(FileRow::to_json).collect()),
        );
        o.insert(
            "outputs".to_owned(),
            Json::Arr(outputs.iter().map(FileRow::to_json).collect()),
        );
        Json::Obj(o)
    }
}
