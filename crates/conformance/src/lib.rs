//! The BDD runner, the honesty meta-gate, the §28.2 fixture runner, and the
//! conformance case registry (R2, R3, SPEC.md §27.7, §27.8, §28.2).
//!
//! Every registered ID has exactly one scenario and exactly one test named
//! `conformance_<id>`; each test dispatches into [`cases::run`], which
//! panics for an ID with no wired case so a registered capability cannot
//! pass silently before it is implemented.

#![deny(missing_docs)]

pub mod cases;
pub mod fixtures;
pub mod meta;
pub mod runner;
pub mod schema;

pub mod support;

pub use meta::{check_honesty, HonestyReport};
pub use runner::{scenarios_in, Scenario, SuiteReport};

use std::collections::BTreeSet;
use std::path::Path;

/// Every `#[test]` function name in the workspace, read from the source
/// (running `cargo test` recursively would deadlock on the target lock).
#[must_use]
pub fn workspace_test_names(root: &Path) -> BTreeSet<String> {
    let (names, _flagged) = workspace_test_names_with_flags(root);
    names
}

/// One scanned Rust source file: its tests, and which of them are disabled
/// or conditional.
#[derive(Debug, Default, Clone)]
pub struct ScannedTests {
    /// Every function carrying `#[test]` in its attribute block.
    pub names: BTreeSet<String>,
    /// The subset whose attribute block also carries `#[ignore ...]`,
    /// `#[cfg(...)]`, or `#[cfg_attr(...)]`, or that lives in a file or
    /// module behind a `cfg` (§27.8: neither ignored nor feature-gated).
    pub flagged: BTreeSet<String>,
    /// Modules declared behind `#[cfg(...)]` in this file (`mod name;`).
    pub gated_modules: BTreeSet<String>,
    /// Whether the file itself opens with `#![cfg(...)]`.
    pub file_gated: bool,
    /// Whether an inline `mod name { ... }` behind a non-`cfg(test)` gate
    /// was seen; every later test in the file is treated as gated.
    pub inline_gated: bool,
}

/// Scan one Rust source text for tests, attribute-block-aware: every
/// attribute line (possibly spanning several lines) between one item and
/// the next belongs to the block of the item that follows.
#[must_use]
pub fn scan_tests(text: &str) -> ScannedTests {
    let mut scanned = ScannedTests::default();
    let mut block: Vec<String> = Vec::new();
    let mut open_attribute: Option<(String, i32)> = None;
    for raw in text.lines() {
        let line = raw.trim();
        if let Some((mut pending, mut depth)) = open_attribute.take() {
            pending.push(' ');
            pending.push_str(line);
            depth += bracket_delta(line);
            if depth > 0 {
                open_attribute = Some((pending, depth));
            } else {
                block.push(pending);
            }
            continue;
        }
        if line.starts_with("#![cfg(") {
            scanned.file_gated = true;
            continue;
        }
        if line.starts_with("#[") {
            let depth = bracket_delta(line);
            if depth > 0 {
                open_attribute = Some((line.to_owned(), depth));
            } else {
                block.push(line.to_owned());
            }
            continue;
        }
        if line.starts_with("//") || line.is_empty() {
            // Comments and blank lines do not end an attribute block.
            continue;
        }
        let item = line
            .trim_start_matches("pub ")
            .trim_start_matches("pub(crate) ")
            .trim_start_matches("async ")
            .trim_start_matches("const ")
            .trim_start_matches("unsafe ")
            .trim_start_matches("extern \"C\" ");
        if let Some(rest) = item.strip_prefix("fn ") {
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            let is_test = block.iter().any(|attribute| {
                attribute == "#[test]"
                    || attribute.starts_with("#[test ")
                    || (attribute.starts_with("#[cfg_attr(") && attribute.contains("test"))
            });
            if is_test && !name.is_empty() {
                let disabled = scanned.file_gated
                    || scanned.inline_gated
                    || block.iter().any(|attribute| {
                        attribute.starts_with("#[ignore")
                            || attribute.starts_with("#[cfg(")
                            || attribute.starts_with("#[cfg_attr(")
                    });
                if disabled {
                    scanned.flagged.insert(name.clone());
                }
                scanned.names.insert(name);
            }
        } else if let Some(rest) = item.strip_prefix("mod ") {
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            let gated = block.iter().any(|attribute| {
                (attribute.starts_with("#[cfg(") && attribute != "#[cfg(test)]")
                    || attribute.starts_with("#[cfg_attr(")
            });
            if gated && !name.is_empty() {
                if rest.contains('{') {
                    scanned.inline_gated = true;
                } else {
                    scanned.gated_modules.insert(name);
                }
            }
        }
        block.clear();
    }
    scanned
}

fn bracket_delta(line: &str) -> i32 {
    let mut depth = 0i32;
    for byte in line.bytes() {
        match byte {
            b'[' | b'(' => depth += 1,
            b']' | b')' => depth -= 1,
            _ => {}
        }
    }
    depth
}

/// The test names plus the subset that is ignored or feature-gated,
/// including tests inside files declared behind a `cfg` by a sibling
/// `mod` declaration.
#[must_use]
pub fn workspace_test_names_with_flags(root: &Path) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut names = BTreeSet::new();
    let mut flagged = BTreeSet::new();
    let mut per_file: Vec<(std::path::PathBuf, ScannedTests)> = Vec::new();
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
                per_file.push((path, scan_tests(&text)));
            }
        }
    }
    // A `#[cfg(...)] mod name;` gates `name.rs` and `name/mod.rs` beside it.
    let mut gated_files: BTreeSet<std::path::PathBuf> = BTreeSet::new();
    for (path, scanned) in &per_file {
        let Some(directory) = path.parent() else {
            continue;
        };
        let base = if path
            .file_name()
            .is_some_and(|name| name == "mod.rs" || name == "lib.rs" || name == "main.rs")
        {
            directory.to_path_buf()
        } else {
            directory.join(path.file_stem().unwrap_or_default())
        };
        for module in &scanned.gated_modules {
            gated_files.insert(base.join(format!("{module}.rs")));
            gated_files.insert(base.join(module).join("mod.rs"));
        }
    }
    for (path, scanned) in &per_file {
        let gated = gated_files.contains(path);
        for name in &scanned.names {
            names.insert(name.clone());
            if gated || scanned.flagged.contains(name) {
                flagged.insert(name.clone());
            }
        }
    }
    (names, flagged)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn attribute_blocks_are_read_whole() {
        let ignore_word = format!("#[{}]", "ignore");
        let source = format!(
            "#[test]\nfn plain() {{}}\n\n{ignore_word}\n#[test]\nfn ignored_first() {{}}\n\n#[test]\n{ignore_word}\nfn ignored_second() {{}}\n\n#[test]\n#[cfg_attr(\n    windows,\n    {}\n)]\nfn attr_multiline() {{}}\n\n#[cfg(feature = \"x\")]\n#[test]\nfn gated() {{}}\n\n#[test]\n// a comment between\nfn commented() {{}}\n\n#[cfg(feature = \"y\")]\nmod hidden;\n",
            "ignore"
        );
        let scanned = scan_tests(&source);
        let expect: BTreeSet<String> = [
            "plain",
            "ignored_first",
            "ignored_second",
            "attr_multiline",
            "gated",
            "commented",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect();
        assert_eq!(scanned.names, expect);
        let flagged: BTreeSet<String> =
            ["ignored_first", "ignored_second", "attr_multiline", "gated"]
                .into_iter()
                .map(str::to_owned)
                .collect();
        assert_eq!(scanned.flagged, flagged);
        assert_eq!(
            scanned.gated_modules,
            ["hidden".to_owned()].into_iter().collect()
        );
        assert!(!scanned.file_gated);
        assert!(scan_tests("#![cfg(test)]\n#[test]\nfn f() {}\n")
            .flagged
            .contains("f"));
        let inline = scan_tests(
            "#[cfg(feature = \"z\")]\nmod inner {\n    #[test]\n    fn conformance_zz_01() {}\n}\n",
        );
        assert!(inline.flagged.contains("conformance_zz_01"));
        let plain_tests =
            scan_tests("#[cfg(test)]\nmod tests {\n    #[test]\n    fn unit() {}\n}\n");
        assert!(plain_tests.flagged.is_empty());
    }
}
