//! The backends (SPEC.md §18, §19): canonical Lean and LaTeX generated from
//! one linked IR (I7), with complete output coverage and source mappings
//! (I13). Neither backend accepts an opaque bypass (I6).

pub mod core;
pub mod latex;
pub mod lean;
pub mod lean_tokens;
pub mod pdf;

use std::collections::BTreeMap;

use crate::artifact::source_map::{MapRole, MapSource, Mapping, SourceMap};
use crate::source::coverage::{Origin, OutputRow};

/// Mechanically check output coverage closure (§19.6, §20.5): every
/// non-whitespace byte of the generated text lies in exactly one row, rows
/// never overlap, and every row lies inside the text. The error names the
/// first offending byte range.
pub fn check_output_closure(text: &str, rows: &[OutputRow]) -> Result<(), String> {
    let mut sorted: Vec<&OutputRow> = rows.iter().collect();
    sorted.sort_by_key(|row| (row.byte_start, row.byte_end));
    let mut cursor = 0usize;
    let bytes = text.as_bytes();
    let first_uncovered = |from: usize, to: usize| -> Option<usize> {
        (from..to.min(bytes.len())).find(|&index| !bytes[index].is_ascii_whitespace())
    };
    for row in &sorted {
        if row.byte_end < row.byte_start || row.byte_end > bytes.len() {
            return Err(format!(
                "coverage row {}..{} lies outside the {}-byte output",
                row.byte_start,
                row.byte_end,
                bytes.len()
            ));
        }
        if row.byte_start < cursor {
            return Err(format!(
                "coverage overlap at bytes {}..{}",
                row.byte_start,
                cursor.min(row.byte_end)
            ));
        }
        if let Some(gap) = first_uncovered(cursor, row.byte_start) {
            let end = (gap..row.byte_start)
                .find(|&index| bytes[index].is_ascii_whitespace())
                .unwrap_or(row.byte_start);
            return Err(format!("coverage gap at bytes {gap}..{end}"));
        }
        cursor = row.byte_end;
    }
    if let Some(gap) = first_uncovered(cursor, bytes.len()) {
        let end = (gap..bytes.len())
            .find(|&index| bytes[index].is_ascii_whitespace())
            .unwrap_or(bytes.len());
        return Err(format!("coverage gap at bytes {gap}..{end}"));
    }
    Ok(())
}

/// Where an emitted piece traces to (§20.3).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum EmitSource {
    /// A byte range of the module source file.
    File(usize, usize),
    /// A glossary entry origin.
    Glossary {
        /// The package ID.
        package: String,
        /// The local entry ID.
        entry: String,
    },
    /// An explicit synthetic origin such as `core:lean-preamble/1`.
    Synthetic(String),
}

/// One emitted, traced piece.
#[derive(Debug, Clone)]
struct Piece {
    start: usize,
    end: usize,
    kind: String,
    origin: Origin,
    source: EmitSource,
    role: MapRole,
    node: usize,
}

/// A text emitter that traces every non-whitespace piece to an origin.
#[derive(Debug, Default)]
pub struct Emitter {
    text: String,
    pieces: Vec<Piece>,
    node_kinds: Vec<String>,
}

impl Emitter {
    /// A fresh emitter.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate an IR node row (§20.3).
    pub fn node(&mut self, kind: &str) -> usize {
        self.node_kinds.push(kind.to_owned());
        self.node_kinds.len() - 1
    }

    /// Emit whitespace or a newline; never traced, never covered.
    pub fn ws(&mut self, text: &str) {
        debug_assert!(text.chars().all(|c| c == ' ' || c == '\n'));
        self.text.push_str(text);
    }

    /// Emit one traced piece.
    pub fn piece(
        &mut self,
        text: &str,
        kind: &str,
        origin: Origin,
        source: EmitSource,
        role: MapRole,
        node: usize,
    ) {
        let start = self.text.len();
        self.text.push_str(text);
        self.pieces.push(Piece {
            start,
            end: self.text.len(),
            kind: kind.to_owned(),
            origin,
            source,
            role,
            node,
        });
    }

    /// The emitted text.
    #[must_use]
    pub fn text(&self) -> &str {
        &self.text
    }

    /// The current byte position.
    #[must_use]
    pub fn position(&self) -> usize {
        self.text.len()
    }

    /// The output coverage rows, sorted by byte start (§20.5).
    #[must_use]
    pub fn coverage_rows(&self) -> Vec<OutputRow> {
        let mut rows: Vec<OutputRow> = self
            .pieces
            .iter()
            .map(|piece| OutputRow {
                byte_start: piece.start,
                byte_end: piece.end,
                kind: piece.kind.clone(),
                origin: piece.origin.clone(),
            })
            .collect();
        rows.sort_by_key(|row| (row.byte_start, row.byte_end));
        rows
    }

    /// Fold this emitter's pieces into a module source map under one
    /// artifact row (§20.3).
    pub fn fold_into_map(&self, map: &mut SourceMap, artifact_id: usize, module_source_id: usize) {
        let mut source_rows: BTreeMap<EmitSource, usize> = BTreeMap::new();
        for piece in &self.pieces {
            let source_row = match &piece.source {
                EmitSource::File(..) => module_source_id,
                other => match source_rows.get(other) {
                    Some(&id) => id,
                    None => {
                        let id = map.sources.len();
                        let row = match other {
                            EmitSource::Glossary { package, entry } => MapSource::Glossary {
                                id,
                                package: package.clone(),
                                entry: entry.clone(),
                            },
                            EmitSource::Synthetic(origin) => MapSource::Synthetic {
                                id,
                                origin: origin.clone(),
                            },
                            EmitSource::File(..) => unreachable!("handled above"),
                        };
                        map.sources.push(row);
                        source_rows.insert(other.clone(), id);
                        id
                    }
                },
            };
            let node_id = map.nodes.len() + piece.node;
            map.mappings.push(Mapping {
                artifact: artifact_id,
                gen_start: piece.start,
                gen_end: piece.end,
                source: source_row,
                src_range: match piece.source {
                    EmitSource::File(start, end) => Some((start, end)),
                    _ => None,
                },
                node: node_id,
                role: piece.role,
            });
        }
        for kind in &self.node_kinds {
            map.nodes.push(crate::artifact::source_map::MapNode {
                id: map.nodes.len(),
                kind: kind.clone(),
            });
        }
        map.mappings
            .sort_by_key(|mapping| (mapping.artifact, mapping.gen_start, mapping.gen_end));
    }
}
