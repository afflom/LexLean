//! Coverage records (SPEC.md §20.5, §19.6): every non-whitespace source atom
//! and every canonical output token carries exactly one origin.

use std::collections::BTreeMap;

use crate::artifact::canonical_json::Json;
use crate::source::atom::AtomClass;

/// One closed coverage origin: what accounts for a token (I1, I2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Origin {
    /// A selected glossary form.
    Form {
        /// The package ID.
        package: String,
        /// The local entry ID.
        entry: String,
        /// The form ID.
        form: String,
    },
    /// A scoped local declaration or occurrence.
    Local(usize),
    /// The core numeric constructor.
    Numeral,
    /// A core structural entry selected as structure (controls, braces,
    /// environment names, punctuation).
    Structural {
        /// The package ID, always `lexlean.core`.
        package: String,
        /// The local entry ID.
        entry: String,
    },
    /// Structural metadata owned by a structural construct: component IDs,
    /// module names, package references, qualified IDs, binder spellings.
    Metadata {
        /// The qualified ID of the owning structural entry.
        owner: String,
    },
    /// A renderer-token emission (output only).
    RendererToken(String),
    /// A document declaration reference.
    Reference {
        /// The module name.
        module: String,
        /// The component ID.
        component: String,
    },
    /// An explicit synthetic origin (output boilerplate).
    Synthetic(String),
}

impl Origin {
    /// The canonical JSON object.
    #[must_use]
    pub fn to_json(&self) -> Json {
        match self {
            Self::Form {
                package,
                entry,
                form,
            } => Json::object(vec![
                ("kind", Json::Str("form".to_owned())),
                ("package", Json::Str(package.clone())),
                ("entry", Json::Str(entry.clone())),
                ("form", Json::Str(form.clone())),
            ]),
            Self::Local(id) => Json::object(vec![
                ("kind", Json::Str("local".to_owned())),
                ("local", Json::from_usize(*id)),
            ]),
            Self::Numeral => Json::object(vec![("kind", Json::Str("numeral".to_owned()))]),
            Self::Structural { package, entry } => Json::object(vec![
                ("kind", Json::Str("structural".to_owned())),
                ("package", Json::Str(package.clone())),
                ("entry", Json::Str(entry.clone())),
            ]),
            Self::Metadata { owner } => Json::object(vec![
                ("kind", Json::Str("metadata".to_owned())),
                ("owner", Json::Str(owner.clone())),
            ]),
            Self::RendererToken(token) => Json::object(vec![
                ("kind", Json::Str("renderer-token".to_owned())),
                ("token", Json::Str(token.clone())),
            ]),
            Self::Reference { module, component } => Json::object(vec![
                ("kind", Json::Str("reference".to_owned())),
                ("module", Json::Str(module.clone())),
                ("component", Json::Str(component.clone())),
            ]),
            Self::Synthetic(origin) => Json::object(vec![
                ("kind", Json::Str("synthetic".to_owned())),
                ("origin", Json::Str(origin.clone())),
            ]),
        }
    }
}

/// One source coverage row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceRow {
    /// Project-relative source path.
    pub path: String,
    /// Start byte in the normalized source.
    pub byte_start: usize,
    /// End byte, exclusive.
    pub byte_end: usize,
    /// The primitive atom class.
    pub class: AtomClass,
    /// The one selected binding.
    pub binding: Origin,
}

/// One output coverage row (canonical LaTeX or generated Lean).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutputRow {
    /// Start byte in the artifact.
    pub byte_start: usize,
    /// End byte, exclusive.
    pub byte_end: usize,
    /// The output token kind.
    pub kind: String,
    /// The origin.
    pub origin: Origin,
}

/// The complete coverage record for one module (§20.5).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Coverage {
    /// The source module name.
    pub module: String,
    /// Source rows sorted by `(path, byte_start)`; non-whitespace rows are
    /// mandatory and whitespace rows are not emitted.
    pub source: Vec<SourceRow>,
    /// Canonical LaTeX rows sorted by `byte_start`.
    pub latex: Vec<OutputRow>,
    /// Generated Lean rows sorted by `byte_start`.
    pub lean: Vec<OutputRow>,
}

impl Coverage {
    /// The canonical JSON object.
    #[must_use]
    pub fn to_json(&self) -> Json {
        let mut o = BTreeMap::new();
        o.insert(
            "spec".to_owned(),
            Json::Str("lexlean/coverage/1".to_owned()),
        );
        o.insert("module".to_owned(), Json::Str(self.module.clone()));
        o.insert(
            "source".to_owned(),
            Json::Arr(
                self.source
                    .iter()
                    .map(|row| {
                        Json::object(vec![
                            ("path", Json::Str(row.path.clone())),
                            ("byte_start", Json::from_usize(row.byte_start)),
                            ("byte_end", Json::from_usize(row.byte_end)),
                            ("class", Json::Str(row.class.as_str().to_owned())),
                            ("binding", row.binding.to_json()),
                        ])
                    })
                    .collect(),
            ),
        );
        for (key, rows) in [("latex", &self.latex), ("lean", &self.lean)] {
            o.insert(
                key.to_owned(),
                Json::Arr(
                    rows.iter()
                        .map(|row| {
                            Json::object(vec![
                                ("byte_start", Json::from_usize(row.byte_start)),
                                ("byte_end", Json::from_usize(row.byte_end)),
                                ("kind", Json::Str(row.kind.clone())),
                                ("origin", row.origin.to_json()),
                            ])
                        })
                        .collect(),
                ),
            );
        }
        Json::Obj(o)
    }

    /// Check the source rows for gaps or overlaps against the scanned atoms
    /// of one file: every non-whitespace atom is covered exactly once (I1).
    /// A violation is an internal invariant failure (§20.5).
    pub fn check_source_closure(
        &self,
        path: &str,
        atoms: &[crate::source::atom::Atom],
    ) -> Result<(), String> {
        let mut rows: Vec<&SourceRow> = self.source.iter().filter(|row| row.path == path).collect();
        rows.sort_by_key(|row| row.byte_start);
        for pair in rows.windows(2) {
            if pair[1].byte_start < pair[0].byte_end {
                return Err(format!(
                    "coverage overlap in {path} at bytes {}..{}",
                    pair[1].byte_start, pair[0].byte_end
                ));
            }
        }
        for atom in atoms {
            if atom.class == AtomClass::Whitespace {
                continue;
            }
            let covered = rows
                .iter()
                .any(|row| row.byte_start <= atom.byte_start && atom.byte_end <= row.byte_end);
            if !covered {
                return Err(format!(
                    "coverage gap in {path} at bytes {}..{} ({:?})",
                    atom.byte_start, atom.byte_end, atom.text
                ));
            }
        }
        Ok(())
    }
}
