//! Source maps (SPEC.md §20.3) and the Lean diagnostic remapping rule
//! (§20.4).

use std::collections::BTreeMap;

use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::Sha256Digest;

/// One originating source in a module map.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MapSource {
    /// A project source file.
    File {
        /// Row ID referenced by mappings.
        id: usize,
        /// Project-relative path.
        path: String,
        /// Digest of the normalized bytes.
        sha256: Sha256Digest,
    },
    /// A glossary entry origin (canonical forms, renderer data).
    Glossary {
        /// Row ID referenced by mappings.
        id: usize,
        /// Package ID.
        package: String,
        /// Local entry ID.
        entry: String,
    },
    /// An explicit synthetic origin such as `core:lean-preamble/1`; never a
    /// fabricated source span (§20.3).
    Synthetic {
        /// Row ID referenced by mappings.
        id: usize,
        /// The synthetic origin tag.
        origin: String,
    },
}

impl MapSource {
    /// The row ID.
    #[must_use]
    pub fn id(&self) -> usize {
        match self {
            Self::File { id, .. } | Self::Glossary { id, .. } | Self::Synthetic { id, .. } => *id,
        }
    }

    /// Is this a synthetic origin? Ties prefer non-synthetic (§20.4).
    #[must_use]
    pub fn is_synthetic(&self) -> bool {
        matches!(self, Self::Synthetic { .. })
    }

    fn to_json(&self) -> Json {
        let mut o = BTreeMap::new();
        match self {
            Self::File { id, path, sha256 } => {
                o.insert("id".to_owned(), Json::from_usize(*id));
                o.insert("kind".to_owned(), Json::Str("file".to_owned()));
                o.insert("path".to_owned(), Json::Str(path.clone()));
                o.insert("sha256".to_owned(), Json::Str(sha256.to_hex()));
            }
            Self::Glossary { id, package, entry } => {
                o.insert("id".to_owned(), Json::from_usize(*id));
                o.insert("kind".to_owned(), Json::Str("glossary".to_owned()));
                o.insert("package".to_owned(), Json::Str(package.clone()));
                o.insert("entry".to_owned(), Json::Str(entry.clone()));
            }
            Self::Synthetic { id, origin } => {
                o.insert("id".to_owned(), Json::from_usize(*id));
                o.insert("kind".to_owned(), Json::Str("synthetic".to_owned()));
                o.insert("origin".to_owned(), Json::Str(origin.clone()));
            }
        }
        Json::Obj(o)
    }
}

/// A generated artifact a mapping points into.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MapArtifact {
    /// Row ID referenced by mappings.
    pub id: usize,
    /// `lean` or `tex`.
    pub kind: ArtifactKind,
    /// Build-relative path.
    pub path: String,
}

/// The two mapped artifact kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArtifactKind {
    /// Generated Lean source.
    Lean,
    /// Canonical LaTeX.
    Tex,
}

impl ArtifactKind {
    /// The schema token.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Lean => "lean",
            Self::Tex => "tex",
        }
    }
}

/// One IR node row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MapNode {
    /// Stable node ID.
    pub id: usize,
    /// The closed IR node kind name.
    pub kind: String,
}

/// A mapping role (§20.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MapRole {
    /// A whole declaration.
    Declaration,
    /// A binder.
    Binder,
    /// A term.
    Term,
    /// A proof step.
    Proof,
    /// Document structure.
    Structure,
    /// Renderer-token output.
    Renderer,
    /// Synthetic boilerplate.
    Synthetic,
}

impl MapRole {
    /// The schema token.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Declaration => "declaration",
            Self::Binder => "binder",
            Self::Term => "term",
            Self::Proof => "proof",
            Self::Structure => "structure",
            Self::Renderer => "renderer",
            Self::Synthetic => "synthetic",
        }
    }
}

/// One mapping row: a generated half-open byte range traced to an origin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mapping {
    /// Artifact row ID.
    pub artifact: usize,
    /// Generated range start.
    pub gen_start: usize,
    /// Generated range end, exclusive.
    pub gen_end: usize,
    /// Source row ID.
    pub source: usize,
    /// Source byte range, absent for glossary and synthetic origins.
    pub src_range: Option<(usize, usize)>,
    /// IR node row ID.
    pub node: usize,
    /// The role.
    pub role: MapRole,
}

/// A complete module source map (§20.3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceMap {
    /// The project source ID.
    pub source_id: Sha256Digest,
    /// The project semantic ID.
    pub semantic_id: Sha256Digest,
    /// The source module name.
    pub module: String,
    /// Origin rows.
    pub sources: Vec<MapSource>,
    /// Artifact rows.
    pub artifacts: Vec<MapArtifact>,
    /// IR node rows.
    pub nodes: Vec<MapNode>,
    /// Mapping rows in `(artifact, gen_start, gen_end)` order.
    pub mappings: Vec<Mapping>,
}

impl SourceMap {
    /// The canonical JSON object.
    #[must_use]
    pub fn to_json(&self) -> Json {
        let mut o = BTreeMap::new();
        o.insert(
            "spec".to_owned(),
            Json::Str("lexlean/source-map/1".to_owned()),
        );
        o.insert("source_id".to_owned(), Json::Str(self.source_id.to_hex()));
        o.insert(
            "semantic_id".to_owned(),
            Json::Str(self.semantic_id.to_hex()),
        );
        o.insert("module".to_owned(), Json::Str(self.module.clone()));
        o.insert(
            "sources".to_owned(),
            Json::Arr(self.sources.iter().map(MapSource::to_json).collect()),
        );
        o.insert(
            "artifacts".to_owned(),
            Json::Arr(
                self.artifacts
                    .iter()
                    .map(|artifact| {
                        Json::object(vec![
                            ("id", Json::from_usize(artifact.id)),
                            ("kind", Json::Str(artifact.kind.as_str().to_owned())),
                            ("path", Json::Str(artifact.path.clone())),
                        ])
                    })
                    .collect(),
            ),
        );
        o.insert(
            "nodes".to_owned(),
            Json::Arr(
                self.nodes
                    .iter()
                    .map(|node| {
                        Json::object(vec![
                            ("id", Json::from_usize(node.id)),
                            ("kind", Json::Str(node.kind.clone())),
                        ])
                    })
                    .collect(),
            ),
        );
        o.insert(
            "mappings".to_owned(),
            Json::Arr(
                self.mappings
                    .iter()
                    .map(|mapping| {
                        let mut m = BTreeMap::new();
                        m.insert("artifact".to_owned(), Json::from_usize(mapping.artifact));
                        m.insert("gen_start".to_owned(), Json::from_usize(mapping.gen_start));
                        m.insert("gen_end".to_owned(), Json::from_usize(mapping.gen_end));
                        m.insert("source".to_owned(), Json::from_usize(mapping.source));
                        if let Some((start, end)) = mapping.src_range {
                            m.insert("src_start".to_owned(), Json::from_usize(start));
                            m.insert("src_end".to_owned(), Json::from_usize(end));
                        }
                        m.insert("node".to_owned(), Json::from_usize(mapping.node));
                        m.insert(
                            "role".to_owned(),
                            Json::Str(mapping.role.as_str().to_owned()),
                        );
                        Json::Obj(m)
                    })
                    .collect(),
            ),
        );
        Json::Obj(o)
    }

    /// Select the mapping for a reported generated-byte position (§20.4):
    /// the smallest enclosing generated mapping, ties resolved by shortest
    /// generated range, then non-synthetic before synthetic, then lowest
    /// stable IR node ID.
    #[must_use]
    pub fn remap(&self, artifact_id: usize, byte_position: usize) -> Option<&Mapping> {
        let synthetic: Vec<bool> = {
            let max_id = self.sources.iter().map(MapSource::id).max().unwrap_or(0);
            let mut flags = vec![true; max_id + 1];
            for source in &self.sources {
                flags[source.id()] = source.is_synthetic();
            }
            flags
        };
        self.mappings
            .iter()
            .filter(|mapping| {
                mapping.artifact == artifact_id
                    && mapping.gen_start <= byte_position
                    && byte_position < mapping.gen_end
            })
            .min_by_key(|mapping| {
                (
                    mapping.gen_end - mapping.gen_start,
                    synthetic.get(mapping.source).copied().unwrap_or(true),
                    mapping.node,
                )
            })
    }
}
