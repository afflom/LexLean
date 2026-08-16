//! The BDD runner, the honesty meta-gate, and the conformance case registry
//! (R2, R3, SPEC.md §27.7, §27.8).
//!
//! Every registered ID has exactly one scenario and exactly one test named
//! `conformance_<id>`; each test dispatches into [`cases::run`], which
//! panics for an ID with no wired case so a registered capability cannot
//! pass silently before it is implemented.

#![deny(missing_docs)]

pub mod cases;
pub mod meta;
pub mod runner;
pub mod support;

pub use meta::{check_honesty, HonestyReport};
pub use runner::{scenarios_in, Scenario, SuiteReport};

use std::collections::BTreeSet;
use std::path::Path;

/// Every `#[test]` function name in the workspace, read from the source
/// (running `cargo test` recursively would deadlock on the target lock).
/// The scan also records ignore and cfg attributes adjacent
/// to conformance tests, which the meta-gate rejects (§27.8).
#[must_use]
pub fn workspace_test_names(root: &Path) -> BTreeSet<String> {
    let (names, _flagged) = workspace_test_names_with_flags(root);
    names
}

/// The test names plus the subset that is ignored or feature-gated.
#[must_use]
pub fn workspace_test_names_with_flags(root: &Path) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut names = BTreeSet::new();
    let mut flagged = BTreeSet::new();
    let mut stack = vec![root.join("crates"), root.join("xtask")];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                if path.file_name().is_some_and(|name| name == "target") {
                    continue;
                }
                stack.push(path);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                let Ok(text) = std::fs::read_to_string(&path) else {
                    continue;
                };
                let mut armed = false;
                let mut poisoned = false;
                for line in text.lines() {
                    let line = line.trim();
                    if line == "#[test]" {
                        armed = true;
                    } else if armed {
                        if line.starts_with("#[ignore") || line.starts_with("#[cfg(") {
                            poisoned = true;
                        } else if let Some(rest) = line.strip_prefix("fn ") {
                            let name: String = rest
                                .chars()
                                .take_while(|c| c.is_alphanumeric() || *c == '_')
                                .collect();
                            if !name.is_empty() {
                                if poisoned {
                                    flagged.insert(name.clone());
                                }
                                names.insert(name);
                            }
                            armed = false;
                            poisoned = false;
                        } else if !line.starts_with('#') && !line.is_empty() {
                            armed = false;
                            poisoned = false;
                        }
                    }
                }
            }
        }
    }
    (names, flagged)
}
