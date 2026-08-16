//! The §28.2 fixture runner.
//!
//! A fixture is a directory
//!
//! ```text
//! <fixture>/
//! ├── project/            the complete input project (symlinks preserved)
//! ├── expected/
//! │   ├── command.json    the canonical command-result of the (final) invocation
//! │   ├── diagnostics.json its diagnostics array alone
//! │   ├── artifacts.json  every published artifact file, sorted
//! │   └── hashes.toml     platform-independent hashes; process-bound files listed apart
//! ├── toolchain/          optional: executables overlaying the pinned toolchain's bin/
//! ├── overlay/<step>/     optional: files copied over the project before invocation <step>
//! └── case.toml
//! ```
//!
//! `case.toml` carries exactly the §28.2 keys (`spec`, `command`, `args`,
//! `expected_exit`, `expect_artifacts`) plus, for a sequence fixture, sorted
//! `[[invocation]]` rows whose last row equals the top-level command. Every
//! invocation runs the CLI entry point (`lexlean::cli::run`, the same
//! function `main` calls) with `--diagnostic-format json` from a temporary
//! copy of `project/`; the runner compares the exit code, the canonical
//! command-result JSON with the temporary root replaced by `$PROJECT` and
//! attestation IDs by `$ATTESTATION`, the diagnostics array, and the sorted
//! artifact list. Expected files are rewritten only by
//! `cargo xtask check-fixtures --write` (§28.3).

use std::collections::BTreeMap;
use std::path::Path;

use camino::{Utf8Path, Utf8PathBuf};
use lexlean::artifact::canonical_json::Json;
use lexlean::artifact::content_id::Sha256Digest;

use crate::support;

/// The exact schema tag of `case.toml`.
pub const CASE_SPEC: &str = "lexlean/test-case/1";

/// One CLI invocation of a fixture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Invocation {
    /// The 1-based step number.
    pub step: u64,
    /// The subcommand.
    pub command: String,
    /// Its arguments.
    pub args: Vec<String>,
    /// The exit code the invocation must return.
    pub expected_exit: i32,
    /// Whether the invocation must publish artifacts.
    pub expect_artifacts: bool,
}

/// A parsed `case.toml`.
#[derive(Debug, Clone)]
pub struct Case {
    /// The fixture directory.
    pub dir: Utf8PathBuf,
    /// The invocations in step order; a single-command fixture has one.
    pub invocations: Vec<Invocation>,
}

/// The four expected files of one fixture, as text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expected {
    /// `expected/command.json`.
    pub command_json: String,
    /// `expected/diagnostics.json`.
    pub diagnostics_json: String,
    /// `expected/artifacts.json`.
    pub artifacts_json: String,
    /// `expected/hashes.toml`.
    pub hashes_toml: String,
}

impl Expected {
    /// The file name and text of each expected file.
    #[must_use]
    pub fn files(&self) -> [(&'static str, &str); 4] {
        [
            ("command.json", &self.command_json),
            ("diagnostics.json", &self.diagnostics_json),
            ("artifacts.json", &self.artifacts_json),
            ("hashes.toml", &self.hashes_toml),
        ]
    }
}

/// The observed run of one fixture.
pub struct Observed {
    /// The final invocation's rendered expected files.
    pub expected: Expected,
    /// The diagnostic codes of the final invocation, in order.
    pub codes: Vec<String>,
    /// The exit code of the final invocation.
    pub exit: i32,
    /// The temporary project copy, kept alive for callers that inspect it.
    pub project: support::P,
}

fn read_string(table: &toml::Value, key: &str, context: &str) -> Result<String, String> {
    table
        .get(key)
        .and_then(toml::Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| format!("{context}: `{key}` must be a string"))
}

fn read_args(table: &toml::Value, context: &str) -> Result<Vec<String>, String> {
    let rows = table
        .get("args")
        .and_then(toml::Value::as_array)
        .ok_or_else(|| format!("{context}: `args` must be an array of strings"))?;
    rows.iter()
        .map(|row| {
            row.as_str()
                .map(str::to_owned)
                .ok_or_else(|| format!("{context}: `args` must be an array of strings"))
        })
        .collect()
}

fn read_i32(table: &toml::Value, key: &str, context: &str) -> Result<i32, String> {
    let value = table
        .get(key)
        .and_then(toml::Value::as_integer)
        .ok_or_else(|| format!("{context}: `{key}` must be an integer"))?;
    i32::try_from(value).map_err(|_| format!("{context}: `{key}` is out of range"))
}

fn read_bool(table: &toml::Value, key: &str, context: &str) -> Result<bool, String> {
    table
        .get(key)
        .and_then(toml::Value::as_bool)
        .ok_or_else(|| format!("{context}: `{key}` must be a boolean"))
}

const TOP_KEYS: [&str; 6] = [
    "spec",
    "command",
    "args",
    "expected_exit",
    "expect_artifacts",
    "invocation",
];
const INVOCATION_KEYS: [&str; 5] = [
    "step",
    "command",
    "args",
    "expected_exit",
    "expect_artifacts",
];

/// Parse and validate a fixture's `case.toml`.
///
/// # Errors
///
/// A structural violation of the §28.2 shape, reported with the fixture path.
pub fn load_case(dir: &Utf8Path) -> Result<Case, String> {
    let context = format!("{dir}/case.toml");
    let text = std::fs::read_to_string(dir.join("case.toml").as_std_path())
        .map_err(|error| format!("{context}: {error}"))?;
    let table: toml::Value = text
        .parse()
        .map_err(|error| format!("{context}: {error}"))?;
    let Some(map) = table.as_table() else {
        return Err(format!("{context}: not a table"));
    };
    for key in map.keys() {
        if !TOP_KEYS.contains(&key.as_str()) {
            return Err(format!("{context}: unknown key `{key}` (§28.2)"));
        }
    }
    let spec = read_string(&table, "spec", &context)?;
    if spec != CASE_SPEC {
        return Err(format!("{context}: spec is `{spec}`, not `{CASE_SPEC}`"));
    }
    let top = Invocation {
        step: 0,
        command: read_string(&table, "command", &context)?,
        args: read_args(&table, &context)?,
        expected_exit: read_i32(&table, "expected_exit", &context)?,
        expect_artifacts: read_bool(&table, "expect_artifacts", &context)?,
    };
    if !dir.join("project").as_std_path().is_dir() {
        return Err(format!("{dir}: `project/` is missing (§28.2)"));
    }
    let mut invocations = Vec::new();
    if let Some(rows) = table.get("invocation") {
        let rows = rows
            .as_array()
            .ok_or_else(|| format!("{context}: `invocation` must be an array of tables"))?;
        for (index, row) in rows.iter().enumerate() {
            let row_context = format!("{context}: invocation {}", index + 1);
            let Some(row_map) = row.as_table() else {
                return Err(format!("{row_context}: not a table"));
            };
            for key in row_map.keys() {
                if !INVOCATION_KEYS.contains(&key.as_str()) {
                    return Err(format!("{row_context}: unknown key `{key}`"));
                }
            }
            let step = row
                .get("step")
                .and_then(toml::Value::as_integer)
                .ok_or_else(|| format!("{row_context}: `step` must be an integer"))?;
            let step = u64::try_from(step).map_err(|_| format!("{row_context}: negative step"))?;
            let expected_previous = u64::try_from(index).unwrap_or(u64::MAX);
            if step != expected_previous.saturating_add(1) {
                return Err(format!(
                    "{row_context}: `[[invocation]]` rows are sorted 1, 2, ...; found step {step}"
                ));
            }
            invocations.push(Invocation {
                step,
                command: read_string(row, "command", &row_context)?,
                args: read_args(row, &row_context)?,
                expected_exit: read_i32(row, "expected_exit", &row_context)?,
                expect_artifacts: row
                    .get("expect_artifacts")
                    .map(|value| {
                        value.as_bool().ok_or_else(|| {
                            format!("{row_context}: `expect_artifacts` is a boolean")
                        })
                    })
                    .transpose()?
                    .unwrap_or(false),
            });
        }
        if invocations.len() < 2 {
            return Err(format!(
                "{context}: a sequence fixture has at least two `[[invocation]]` rows"
            ));
        }
        let last = invocations.last().expect("at least two");
        let final_matches = last.command == top.command
            && last.args == top.args
            && last.expected_exit == top.expected_exit
            && last.expect_artifacts == top.expect_artifacts;
        if !final_matches {
            return Err(format!(
                "{context}: the top-level command describes the final invocation and must equal the last `[[invocation]]` row"
            ));
        }
    } else {
        invocations.push(Invocation { step: 1, ..top });
    }
    Ok(Case {
        dir: dir.to_path_buf(),
        invocations,
    })
}

/// Every fixture directory (one containing `case.toml`) under
/// `tests/fixtures` and `tests/negative`, sorted.
#[must_use]
pub fn discover(root: &Utf8Path) -> Vec<Utf8PathBuf> {
    let mut found = Vec::new();
    for base in ["tests/fixtures", "tests/negative"] {
        for entry in walkdir::WalkDir::new(root.join(base).as_std_path())
            .follow_links(false)
            .into_iter()
            .flatten()
        {
            if entry.file_type().is_file() && entry.file_name() == "case.toml" {
                if let Some(parent) = entry.path().parent() {
                    if let Ok(utf8) = Utf8PathBuf::from_path_buf(parent.to_path_buf()) {
                        found.push(utf8);
                    }
                }
            }
        }
    }
    found.sort();
    found
}

/// Copy a tree preserving symlinks as symlinks (a fixture may deliberately
/// contain one, SPEC.md §28.5 "a path symlink").
fn copy_tree_preserving_links(from: &Path, to: &Path) -> Result<(), String> {
    for entry in walkdir::WalkDir::new(from)
        .follow_links(false)
        .into_iter()
        .flatten()
    {
        let relative = entry.path().strip_prefix(from).unwrap_or(entry.path());
        if relative.as_os_str().is_empty() {
            continue;
        }
        let destination = to.join(relative);
        let file_type = entry.file_type();
        let failed = |error: std::io::Error| format!("{}: {error}", destination.display());
        if file_type.is_symlink() {
            let target = std::fs::read_link(entry.path()).map_err(failed)?;
            #[cfg(unix)]
            std::os::unix::fs::symlink(&target, &destination).map_err(failed)?;
            #[cfg(windows)]
            std::os::windows::fs::symlink_file(&target, &destination).map_err(failed)?;
        } else if file_type.is_dir() {
            std::fs::create_dir_all(&destination).map_err(failed)?;
        } else if file_type.is_file() {
            if let Some(parent) = destination.parent() {
                std::fs::create_dir_all(parent).map_err(failed)?;
            }
            std::fs::copy(entry.path(), &destination).map_err(failed)?;
        }
    }
    Ok(())
}

/// Files under `dir` (relative, sorted, `/`-separated).
fn files_under(dir: &Path) -> Vec<String> {
    let mut out = Vec::new();
    for entry in walkdir::WalkDir::new(dir)
        .follow_links(false)
        .into_iter()
        .flatten()
    {
        if entry.file_type().is_file() {
            let relative = entry
                .path()
                .strip_prefix(dir)
                .unwrap_or(entry.path())
                .to_string_lossy()
                .replace('\\', "/");
            out.push(relative);
        }
    }
    out.sort();
    out
}

/// Is this verified-directory-relative path process-bound (§22.8, AR-14)?
fn process_bound(relative_in_artifact: &str) -> bool {
    relative_in_artifact == "attestation.json"
        || relative_in_artifact == "probe/process.json"
        || relative_in_artifact == "audit/process.json"
        || relative_in_artifact.starts_with("oleans/")
        || relative_in_artifact.starts_with("process/")
        || relative_in_artifact.starts_with("pdf/")
}

/// Replace `.lexlean/verified/<hex>` by `.lexlean/verified/$ATTESTATION`.
fn normalize_attestation(text: &str) -> String {
    let marker = "/verified/";
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(position) = rest.find(marker) {
        let after = position + marker.len();
        out.push_str(&rest[..after]);
        let candidate = &rest[after..];
        let hex_len = candidate.bytes().take_while(u8::is_ascii_hexdigit).count();
        if hex_len == 64 {
            out.push_str("$ATTESTATION");
            rest = &candidate[64..];
        } else {
            rest = candidate;
        }
    }
    out.push_str(rest);
    out
}

fn toml_string(text: &str) -> String {
    format!("{:?}", text)
}

/// Run one fixture and return what it produced. Exit codes are asserted
/// against `case.toml`; the expected files are returned for comparison or
/// writing.
///
/// # Errors
///
/// A malformed fixture, a wrong exit code, an artifact contract violation,
/// or a non-JSON command result.
#[allow(clippy::too_many_lines)]
pub fn observe(case: &Case) -> Result<Observed, String> {
    let project = support::P::empty();
    copy_tree_preserving_links(
        case.dir.join("project").as_std_path(),
        project.root.as_std_path(),
    )?;
    let toolchain_dir = case.dir.join("toolchain/bin");
    let fake_home = if toolchain_dir.as_std_path().is_dir() {
        let mut replacements: Vec<(String, Vec<u8>)> = Vec::new();
        for name in files_under(toolchain_dir.as_std_path()) {
            let bytes = std::fs::read(toolchain_dir.join(&name).as_std_path())
                .map_err(|error| format!("{}: {error}", toolchain_dir.join(&name)))?;
            replacements.push((name, bytes));
        }
        Some(support::fake_elan_home(&replacements))
    } else {
        None
    };
    let root_text = project.root.as_str().to_owned();
    let mut final_result: Option<(Invocation, i32, String)> = None;
    let mut run_all = || -> Result<(), String> {
        for invocation in &case.invocations {
            let overlay = case.dir.join("overlay").join(invocation.step.to_string());
            if overlay.as_std_path().is_dir() {
                copy_tree_preserving_links(overlay.as_std_path(), project.root.as_std_path())?;
            }
            let mut argv: Vec<&str> = vec!["--diagnostic-format", "json", &invocation.command];
            argv.extend(invocation.args.iter().map(String::as_str));
            let (exit, stdout, stderr) = support::cli_in(&project.root, &argv);
            if exit != invocation.expected_exit {
                return Err(format!(
                    "{}: step {} `{} {}` exited {exit}, case.toml expects {}\nstdout: {stdout}\nstderr: {stderr}",
                    case.dir,
                    invocation.step,
                    invocation.command,
                    invocation.args.join(" "),
                    invocation.expected_exit
                ));
            }
            final_result = Some((invocation.clone(), exit, stdout));
        }
        Ok(())
    };
    match &fake_home {
        Some(home) => {
            let home_text = home.path().to_string_lossy().into_owned();
            support::with_env(&[("ELAN_HOME", Some(&home_text))], run_all)?;
        }
        None => run_all()?,
    }
    let (invocation, exit, stdout) = final_result.ok_or("a fixture has an invocation")?;
    let normalized = normalize_attestation(&stdout.replace(&root_text, "$PROJECT"));
    let parsed = Json::parse(normalized.as_bytes())
        .map_err(|error| format!("{}: the command result is not JSON: {error}", case.dir))?;
    let Json::Obj(object) = &parsed else {
        return Err(format!("{}: the command result is not an object", case.dir));
    };
    let diagnostics = object
        .get("diagnostics")
        .cloned()
        .ok_or_else(|| format!("{}: the command result has no diagnostics", case.dir))?;
    let codes: Vec<String> = match &diagnostics {
        Json::Arr(rows) => rows
            .iter()
            .filter_map(|row| match row {
                Json::Obj(fields) => match fields.get("code") {
                    Some(Json::Str(code)) => Some(code.clone()),
                    _ => None,
                },
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    };
    let artifact_dirs: Vec<String> = match object.get("artifacts") {
        Some(Json::Arr(rows)) => rows
            .iter()
            .filter_map(|row| match row {
                Json::Str(text) => Some(text.clone()),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    };
    // Enumerate the published files from the un-normalized stdout so the
    // real directory is read; record them normalized.
    let raw_dirs: Vec<String> = match Json::parse(stdout.as_bytes()) {
        Ok(Json::Obj(raw)) => match raw.get("artifacts") {
            Some(Json::Arr(rows)) => rows
                .iter()
                .filter_map(|row| match row {
                    Json::Str(text) => Some(text.clone()),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    let mut artifact_files: Vec<String> = Vec::new();
    let mut platform_independent: BTreeMap<String, String> = BTreeMap::new();
    let mut process_bound_files: Vec<String> = Vec::new();
    for (raw_dir, shown_dir) in raw_dirs.iter().zip(&artifact_dirs) {
        let directory = project.root.join(raw_dir);
        if !directory.as_std_path().is_dir() {
            return Err(format!(
                "{}: the command result names artifact `{raw_dir}` which is not a directory",
                case.dir
            ));
        }
        for relative in files_under(directory.as_std_path()) {
            let shown = format!("{shown_dir}/{relative}");
            artifact_files.push(shown.clone());
            let bytes = std::fs::read(directory.join(&relative).as_std_path())
                .map_err(|error| format!("{shown}: {error}"))?;
            if raw_dir.contains("/verified/") && process_bound(&relative) {
                process_bound_files.push(shown);
            } else {
                platform_independent.insert(shown, Sha256Digest::of(&bytes).to_hex());
            }
        }
    }
    artifact_files.sort();
    process_bound_files.sort();
    let published_root = project.root.join(".lexlean");
    // A failed `verify` legitimately leaves the published build (§22.1 stage
    // 3 precedes Lean); it must never leave a verified directory. Any other
    // command with `expect_artifacts = false` publishes nothing at all.
    let watched: &[&str] = if invocation.command == "verify" {
        &["verified"]
    } else {
        &["build", "verified"]
    };
    let stray: Vec<String> = watched
        .iter()
        .flat_map(|kind| {
            files_under(published_root.join(kind).as_std_path())
                .into_iter()
                .map(move |file| format!(".lexlean/{kind}/{file}"))
        })
        .collect();
    if invocation.expect_artifacts {
        if artifact_files.is_empty() {
            return Err(format!(
                "{}: expect_artifacts = true but the command published nothing",
                case.dir
            ));
        }
    } else if !artifact_dirs.is_empty() || !stray.is_empty() {
        return Err(format!(
            "{}: expect_artifacts = false but artifacts exist: {artifact_dirs:?} {stray:?}",
            case.dir
        ));
    }
    let mut hashes = String::new();
    hashes.push_str("# Platform-independent artifact hashes (compared exactly) and the\n# process-bound files whose bytes vary per host, toolchain build, and\n# compiler executable (presence only). SPEC.md §28.2, §28.4.\n\n[platform_independent]\n");
    for (path, hex) in &platform_independent {
        hashes.push_str(&format!("{} = \"{hex}\"\n", toml_string(path)));
    }
    hashes.push_str("\n[process_bound]\nfiles = [");
    if !process_bound_files.is_empty() {
        hashes.push('\n');
        for path in &process_bound_files {
            hashes.push_str(&format!("    {},\n", toml_string(path)));
        }
    }
    hashes.push_str("]\n");
    let expected = Expected {
        command_json: normalized,
        diagnostics_json: String::from_utf8(diagnostics.to_file_bytes())
            .map_err(|error| error.to_string())?,
        artifacts_json: String::from_utf8(
            Json::Arr(artifact_files.into_iter().map(Json::Str).collect()).to_file_bytes(),
        )
        .map_err(|error| error.to_string())?,
        hashes_toml: hashes,
    };
    Ok(Observed {
        expected,
        codes,
        exit,
        project,
    })
}

/// Read the committed expected files.
///
/// # Errors
///
/// A missing expected file.
pub fn read_expected(dir: &Utf8Path) -> Result<Expected, String> {
    let read = |name: &str| {
        std::fs::read_to_string(dir.join("expected").join(name).as_std_path())
            .map_err(|error| format!("{dir}/expected/{name}: {error}; run `just fixtures-write`"))
    };
    Ok(Expected {
        command_json: read("command.json")?,
        diagnostics_json: read("diagnostics.json")?,
        artifacts_json: read("artifacts.json")?,
        hashes_toml: read("hashes.toml")?,
    })
}

/// Run a fixture and compare it with its committed expectation.
///
/// # Errors
///
/// The first difference, naming the file.
pub fn check(dir: &Utf8Path) -> Result<Observed, String> {
    let case = load_case(dir)?;
    let observed = observe(&case)?;
    let committed = read_expected(dir)?;
    for ((name, expected), (_, actual)) in committed.files().iter().zip(observed.expected.files()) {
        if expected != &actual {
            return Err(format!(
                "{dir}/expected/{name} differs from the observed run (§28.3: golden output changes only through `just fixtures-write`)\n--- expected\n{expected}\n--- observed\n{actual}"
            ));
        }
    }
    for text in observed.expected.files().map(|(_, text)| text) {
        if let Some(line) = text
            .lines()
            .find(|line| line.contains("/tmp/") || line.contains("/home/") || line.contains(":\\"))
        {
            return Err(format!(
                "{dir}: an expected file carries an absolute path: {line}"
            ));
        }
    }
    Ok(observed)
}

/// Run a fixture and write its expected files (the only rewrite path).
///
/// # Errors
///
/// A failed run or a write failure.
pub fn write(dir: &Utf8Path) -> Result<Observed, String> {
    let case = load_case(dir)?;
    let observed = observe(&case)?;
    let expected_dir = dir.join("expected");
    std::fs::create_dir_all(expected_dir.as_std_path())
        .map_err(|error| format!("{expected_dir}: {error}"))?;
    for (name, text) in observed.expected.files() {
        std::fs::write(expected_dir.join(name).as_std_path(), text)
            .map_err(|error| format!("{expected_dir}/{name}: {error}"))?;
    }
    Ok(observed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn attestation_ids_normalize_and_short_hex_survives() {
        let hex = "a".repeat(64);
        let text = format!(".lexlean/verified/{hex}/attestation.json and /verified/abc/x");
        assert_eq!(
            normalize_attestation(&text),
            ".lexlean/verified/$ATTESTATION/attestation.json and /verified/abc/x"
        );
    }

    #[test]
    fn process_bound_classification_matches_section_22_8() {
        for bound in [
            "attestation.json",
            "oleans/A/B.olean",
            "process/lean/A.json",
            "probe/process.json",
            "audit/process.json",
            "pdf/Main.pdf",
        ] {
            assert!(process_bound(bound), "{bound}");
        }
        for free in [
            "build-manifest.json",
            "modules/A/B.lean",
            "audit/output.txt",
            "probe/P.lean",
            "maps/A/B.map.json",
        ] {
            assert!(!process_bound(free), "{free}");
        }
    }
}
