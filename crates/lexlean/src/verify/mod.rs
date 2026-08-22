//! Verification (SPEC.md §22): the complete fixed pipeline, with no
//! optional stage and no suppression. Any failed stage removes the staging
//! tree and produces no verified artifact (I11).
//!
//! Fixed decisions this module makes where the specification leaves the
//! mechanics to the implementation:
//!
//! - **`leanchecker` identity.** The pinned `leanchecker` has no version
//!   flag. Its recorded, checked identity is the normalized output of the
//!   fixed identity probe `lake env <leanchecker> LexLeanIdentityProbe`
//!   (the preflighted executable by absolute path, on a module name no
//!   workspace defines), which the pinned toolchain
//!   answers with exactly one deterministic line and a nonzero exit; the
//!   executable digest is recorded alongside.
//! - **Verified-set reuse.** A verification whose attestation ID already
//!   has a published directory reuses it only after every staged file is
//!   byte-equal to the published one and neither side has extra files.
//! - **Process records.** Every child the pipeline runs (probe, module
//!   compilations, `leanchecker` replays, the audit, and both PDF provider
//!   processes per module) is recorded in the attestation and checked for
//!   unexpected absolute paths.

pub mod axiom;
pub mod child;
pub mod leanchecker;
pub mod source_audit;
pub mod toolchain;
pub mod workspace;

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;

use camino::{Utf8Path, Utf8PathBuf};

use crate::api::{RenderedBuild, RenderedModule};
use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::{attestation_id, Sha256Digest};
use crate::artifact::source_map::{MapRole, Mapping};
use crate::code;
use crate::diagnostic::{Diagnostic, Span};
use crate::error::LexLeanError;
use crate::ir::term::LocalId;
use crate::link::CheckedProject;
use crate::lock::Lock;
use crate::project::Project;
use crate::source::coverage::Origin;
use crate::verify::child::{run as run_child, ChildHome, ChildRecord, ChildSpec, Normalizer};
use crate::verify::toolchain::Toolchain;

/// The outcome of a successful verification.
pub struct VerifyOutcome {
    /// The attestation ID.
    pub attestation_id: Sha256Digest,
    /// The published verified directory.
    pub root: Utf8PathBuf,
}

fn fail(diagnostic: Diagnostic) -> LexLeanError {
    LexLeanError::from_diagnostic(diagnostic)
}

fn internal(message: impl std::fmt::Display) -> Diagnostic {
    Diagnostic::new(code!("LLI9001"), format!("phase verify: {message}"))
}

/// The prose-free generated-source audit (§18.2, LN-11) over one file.
pub fn generated_source_audit(text: &str, allow_print_axioms: bool) -> Result<(), String> {
    source_audit::audit(text, allow_print_axioms)
}

fn generated_core_source_audit(text: &str) -> Result<(), String> {
    source_audit::audit_core(text)
}

fn write_staged(root: &std::path::Path, relative: &str, bytes: &[u8]) -> Result<(), LexLeanError> {
    let destination = root.join(relative);
    if let Some(parent) = destination.parent() {
        std::fs::create_dir_all(parent).map_err(|io_error| {
            fail(Diagnostic::new(
                code!("LLB6003"),
                format!("staging {relative}: {io_error}"),
            ))
        })?;
    }
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&destination)
        .map_err(|io_error| {
            fail(Diagnostic::new(
                code!("LLB6003"),
                format!("staging {relative}: {io_error}"),
            ))
        })?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(|io_error| {
            fail(Diagnostic::new(
                code!("LLB6003"),
                format!("staging {relative}: {io_error}"),
            ))
        })
}

/// One parsed Lean message location: `path:line:col: severity: message`
/// with its indented continuation lines. Lean 4.32.1 prints
/// `path:line:col[-line:col]: severity[(name)]: message`
/// (`Lean.mkErrorStringWithPos`): the end position appears only under
/// `printMessageEndPos`, and named errors carry their error name in
/// parentheses, as in `error(lean.unknownIdentifier)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanMessage {
    /// The reported path as printed.
    pub path: String,
    /// One-based line.
    pub line: usize,
    /// Zero-based column in Unicode scalar values.
    pub column: usize,
    /// `error`, `warning`, or `info`.
    pub severity: String,
    /// The error name Lean printed in parentheses after the severity, when
    /// any (`lean.unknownIdentifier`).
    pub name: Option<String>,
    /// The message text with continuation lines joined by LF.
    pub message: String,
}

/// Parse `severity` or `severity(name)` into its two parts; only Lean's
/// severities open a message.
fn parse_severity(label: &str) -> Option<(String, Option<String>)> {
    let label = label.trim();
    let (severity, name) = match label.split_once('(') {
        Some((severity, rest)) => {
            let name = rest.strip_suffix(')')?;
            if name.is_empty() || name.chars().any(char::is_whitespace) {
                return None;
            }
            (severity, Some(name.to_owned()))
        }
        None => (label, None),
    };
    if !matches!(severity, "error" | "warning" | "info" | "information") {
        return None;
    }
    Some((severity.to_owned(), name))
}

/// Parse a Lean line/column pair.
fn parse_position(line: &str, column: &str) -> Option<(usize, usize)> {
    let line_number = line.trim().parse::<usize>().ok()?;
    let column = column.trim().parse::<usize>().ok()?;
    Some((line_number, column))
}

/// Parse one line as a message opener.
fn parse_message_opener(line: &str) -> Option<LeanMessage> {
    // The path may contain `:` on no supported host, so the split takes
    // the first three fields.
    let mut parts = line.splitn(4, ':');
    let path = parts.next()?;
    let line_field = parts.next()?;
    let column_field = parts.next()?;
    let rest = parts.next()?;
    match column_field.split_once('-') {
        // `line:col-endline:endcol: severity: message`: the column field
        // holds `col-endline` and the fourth field starts with `endcol:`.
        Some((column, end_line)) => {
            let (line_number, column) = parse_position(line_field, column)?;
            end_line.trim().parse::<usize>().ok()?;
            let (end_column, remainder) = rest.split_once(':')?;
            end_column.trim().parse::<usize>().ok()?;
            finish_opener(path, line_number, column, remainder)
        }
        None => {
            let (line_number, column) = parse_position(line_field, column_field)?;
            finish_opener(path, line_number, column, rest)
        }
    }
}

fn finish_opener(path: &str, line: usize, column: usize, rest: &str) -> Option<LeanMessage> {
    let rest = rest.trim_start();
    let (label, message) = rest.split_once(':')?;
    let (severity, name) = parse_severity(label)?;
    Some(LeanMessage {
        path: path.to_owned(),
        line,
        column,
        severity,
        name,
        message: message.trim().to_owned(),
    })
}

/// Parse every Lean message from combined process output (§20.4). Lines
/// that do not open a message continue the previous one.
#[must_use]
pub fn parse_lean_messages(output: &str) -> Vec<LeanMessage> {
    let mut messages: Vec<LeanMessage> = Vec::new();
    for line in output.lines() {
        match parse_message_opener(line) {
            Some(message) => messages.push(message),
            None => {
                if let Some(last) = messages.last_mut() {
                    if !line.trim().is_empty() {
                        last.message.push('\n');
                        last.message.push_str(line.trim_end());
                    }
                }
            }
        }
    }
    messages
}

/// The non-blank output lines preceding the first located message: text
/// no message accounts for (a wrapper's stray line, an unlocated warning).
#[must_use]
pub fn lean_output_preamble(output: &str) -> String {
    output
        .lines()
        .take_while(|line| parse_message_opener(line).is_none())
        .filter(|line| !line.trim().is_empty())
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n")
}

/// The byte offset of a Lean location in generated text: Lean columns count
/// Unicode scalar values (§20.1), so the column is converted per line.
#[must_use]
pub fn lean_position_to_byte(text: &str, line: usize, column: usize) -> Option<usize> {
    let mut offset = 0usize;
    for (index, text_line) in text.split('\n').enumerate() {
        if index + 1 == line {
            let within: usize = text_line.chars().take(column).map(char::len_utf8).sum();
            return Some(offset + within);
        }
        offset += text_line.len() + 1;
    }
    None
}

fn source_span(checked: &CheckedProject, module: &RenderedModule, range: (usize, usize)) -> Span {
    let path = module
        .map
        .sources
        .first()
        .map_or_else(String::new, |source| match source {
            crate::artifact::source_map::MapSource::File { path, .. } => path.clone(),
            _ => String::new(),
        });
    let position = |byte: usize| {
        checked
            .modules
            .get(&module.module)
            .map_or((1, 1), |checked_module| {
                let prefix =
                    &checked_module.normalized[..byte.min(checked_module.normalized.len())];
                let line = prefix.matches('\n').count() + 1;
                let column = prefix
                    .rsplit('\n')
                    .next()
                    .map_or(1, |tail| tail.chars().count() + 1);
                (line, column)
            })
    };
    let (line_start, column_start) = position(range.0);
    let (line_end, column_end) = position(range.1);
    Span {
        path,
        byte_start: range.0,
        byte_end: range.1,
        line_start,
        column_start,
        line_end,
        column_end,
    }
}

/// The source span of one generated declaration (§20.1: the primary
/// location is the thing that failed). The Lean backend emits a
/// declaration's name under the `declaration` role and its own reference
/// origin, mapped to the declaration's whole source range, so the first
/// coverage row carrying that origin under that role locates it. An
/// axiom-policy, replay, or audit failure is about that declaration, not
/// about the project manifest.
fn declaration_span(
    checked: &CheckedProject,
    module: &RenderedModule,
    document_module: &str,
    component: &str,
) -> Option<Span> {
    let origin = Origin::Reference {
        module: document_module.to_owned(),
        component: component.to_owned(),
    };
    module
        .coverage
        .lean
        .iter()
        .filter(|row| row.origin == origin)
        .find_map(|row| {
            let mapping = module.map.remap(0, row.byte_start)?;
            if mapping.role == MapRole::Declaration {
                mapping.src_range
            } else {
                None
            }
        })
        .map(|range| source_span(checked, module, range))
}

/// Anchor an axiom-audit rejection at the declaration it is about, when
/// the parser named one (§20.1). The parser reports the full Lean name
/// `<lean module>.<lean name>`; the declaration owning it is the one whose
/// generated module is the name's prefix.
fn audit_diagnostic(
    checked: &CheckedProject,
    build: &RenderedBuild,
    failure: axiom::AuditFailure,
) -> Diagnostic {
    let Some(full_name) = failure.declaration else {
        return failure.diagnostic;
    };
    for module in &build.modules {
        let Some(lean_name) = full_name
            .strip_prefix(&module.lean_module)
            .and_then(|rest| rest.strip_prefix('.'))
        else {
            continue;
        };
        let document = &checked.modules[&module.module].document;
        for declaration in document.declarations() {
            if declaration.lean_name != lean_name {
                continue;
            }
            if let Some(span) =
                declaration_span(checked, module, &document.name, &declaration.component)
            {
                return failure.diagnostic.with_span(span);
            }
        }
    }
    failure.diagnostic
}

/// The declaration mapping enclosing a generated byte position: the
/// nearest preceding `declaration`-role mapping.
fn enclosing_declaration(module: &RenderedModule, offset: usize) -> Option<&Mapping> {
    module
        .map
        .mappings
        .iter()
        .filter(|mapping| {
            mapping.artifact == 0
                && mapping.role == MapRole::Declaration
                && mapping.gen_start <= offset
        })
        .max_by_key(|mapping| mapping.gen_start)
}

/// Is `c` a character of a generated Lean identifier?
fn is_lean_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// The generated local names (`llv<n>`, `llh<n>`, §17.8, each optionally
/// carrying the `_` prefix an unreferenced binder gets) a Lean message
/// mentions, in first-mention order.
fn generated_names_in(message: &str) -> Vec<String> {
    let mut names: Vec<String> = Vec::new();
    let mut previous: Option<char> = None;
    let mut rest = message;
    while !rest.is_empty() {
        let word: String = rest
            .chars()
            .take_while(|c| is_lean_ident_char(*c))
            .collect();
        if word.is_empty() {
            let mut chars = rest.chars();
            previous = chars.next();
            rest = chars.as_str();
            continue;
        }
        let starts_word = previous.is_none_or(|c| !is_lean_ident_char(c));
        let stem = word.strip_prefix('_').unwrap_or(&word);
        let generated = stem.len() > 3
            && (stem.starts_with("llv") || stem.starts_with("llh"))
            && stem[3..].chars().all(|c| c.is_ascii_digit());
        if starts_word && generated && !names.contains(&word) {
            names.push(word.clone());
        }
        previous = word.chars().next_back();
        rest = &rest[word.len()..];
    }
    names
}

/// Notes mapping generated local names a Lean message mentions back to
/// their source spellings (§17.8: spellings are retained for diagnostics).
/// A generated name is resolved within the declaration enclosing the
/// reported position: its Lean coverage row carries the local's identity,
/// and the source coverage rows (or the proof-introduced spellings) carry
/// the spelling.
fn generated_name_notes(
    checked: &CheckedProject,
    module: &RenderedModule,
    offset: usize,
    message: &str,
) -> Vec<String> {
    let names = generated_names_in(message);
    if names.is_empty() {
        return Vec::new();
    }
    let Some(checked_module) = checked.modules.get(&module.module) else {
        return Vec::new();
    };
    let declaration_start =
        enclosing_declaration(module, offset).map_or(0, |mapping| mapping.gen_start);
    let declaration_end = module
        .map
        .mappings
        .iter()
        .filter(|mapping| {
            mapping.artifact == 0
                && mapping.role == MapRole::Declaration
                && mapping.gen_start > declaration_start
        })
        .map(|mapping| mapping.gen_start)
        .min()
        .unwrap_or(module.lean_text.len());
    let mut notes = Vec::new();
    for name in names {
        let local = module.coverage.lean.iter().find_map(|row| {
            let within = row.byte_start >= declaration_start && row.byte_end <= declaration_end;
            let text = module.lean_text.get(row.byte_start..row.byte_end);
            match (&row.origin, within, text) {
                (Origin::Local(id), true, Some(text)) if text == name => Some(*id),
                _ => None,
            }
        });
        let Some(id) = local else {
            continue;
        };
        let spelling = checked_module
            .coverage_source
            .iter()
            .find(|row| matches!(row.binding, Origin::Local(local) if local == id))
            .and_then(|row| checked_module.normalized.get(row.byte_start..row.byte_end))
            .map(str::to_owned)
            .or_else(|| {
                let id = u64::try_from(id).ok()?;
                checked_module.proof_spellings.get(&LocalId(id)).cloned()
            });
        if let Some(spelling) = spelling {
            if spelling != name {
                notes.push(format!(
                    "generated name `{name}` is the source binder `{spelling}`"
                ));
            }
        }
    }
    notes
}

/// What a module compilation produced, for remapping.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LeanOutcome {
    /// A nonzero exit: every error and warning is a rejection (LLV7002).
    Rejected,
    /// A zero exit with output: every warning or informational message is
    /// a verification failure (LLV7006, §20.2, §22.3).
    Noisy,
}

/// Remap every Lean message location against the generated module maps
/// (§20.4): the smallest enclosing mapping wins; a position no mapping
/// encloses falls back to the enclosing declaration component with the
/// generated range kept as a note. Warnings and errors remap alike; a
/// generated local name the message mentions is explained by a note.
fn remap_lean_output(
    checked: &CheckedProject,
    build: &RenderedBuild,
    module_lean_name: &str,
    output: &str,
    outcome: LeanOutcome,
) -> Vec<Diagnostic> {
    let (code, verb) = match outcome {
        LeanOutcome::Rejected => (code!("LLV7002"), "rejected"),
        LeanOutcome::Noisy => (code!("LLV7006"), "produced unexpected output for"),
    };
    let raw = |text: &str| {
        Diagnostic::new(
            code,
            format!("Lean {verb} `{module_lean_name}`: {}", text.trim_end()),
        )
    };
    let Some(module) = build
        .modules
        .iter()
        .find(|module| module.lean_module == module_lean_name)
    else {
        return vec![raw(output)];
    };
    let mut diagnostics = Vec::new();
    if outcome == LeanOutcome::Noisy {
        let preamble = lean_output_preamble(output);
        if !preamble.is_empty() {
            diagnostics.push(raw(&preamble));
        }
    }
    for message in parse_lean_messages(output) {
        if outcome == LeanOutcome::Rejected && message.severity == "info" {
            continue;
        }
        let kind = match &message.name {
            Some(name) => format!("{} {name}", message.severity),
            None => message.severity.clone(),
        };
        let mut diagnostic = Diagnostic::new(
            code,
            format!(
                "Lean {verb} `{module_lean_name}` ({kind}): {}",
                message.message
            ),
        );
        let offset = lean_position_to_byte(&module.lean_text, message.line, message.column);
        let generated_note = format!(
            "generated location: {}:{}:{}",
            message.path, message.line, message.column
        );
        match offset {
            Some(offset) => {
                match module
                    .map
                    .remap(0, offset)
                    .and_then(|mapping| mapping.src_range)
                {
                    Some(range) => {
                        diagnostic = diagnostic
                            .with_span(source_span(checked, module, range))
                            .with_note(generated_note);
                    }
                    None => {
                        if let Some(range) = enclosing_declaration(module, offset)
                            .and_then(|mapping| mapping.src_range)
                        {
                            diagnostic = diagnostic.with_span(source_span(checked, module, range));
                        }
                        let generated_end = module.lean_text[offset..]
                            .find(char::is_whitespace)
                            .map_or(module.lean_text.len(), |length| offset + length);
                        diagnostic = diagnostic.with_note(format!(
                            "{generated_note} (unmapped generated bytes {offset}..{generated_end})"
                        ));
                    }
                }
                for note in generated_name_notes(checked, module, offset, &message.message) {
                    diagnostic = diagnostic.with_note(note);
                }
            }
            None => {
                diagnostic = diagnostic.with_note(generated_note);
            }
        }
        diagnostics.push(diagnostic);
    }
    if diagnostics.is_empty() {
        diagnostics.push(raw(output));
    }
    diagnostics
}

/// The fixed `leanchecker` identity probe (module documentation): the
/// module name no workspace defines and the exact normalized answer the
/// pinned toolchain gives.
pub const LEANCHECKER_IDENTITY_MODULE: &str = "LexLeanIdentityProbe";
/// The expected normalized identity output.
pub const LEANCHECKER_IDENTITY_OUTPUT: &str =
    "uncaught exception: Could not find any oleans for: LexLeanIdentityProbe\n";

/// Run the identity probe and record its output as `leanchecker`'s
/// version output; a different answer is a toolchain mismatch (LLV7001).
fn leanchecker_identity(
    toolchain: &Toolchain,
    lean_path: &str,
    workspace_root: &Utf8Path,
    limits: &crate::config::Limits,
    normalizer: &Normalizer,
) -> Result<String, Diagnostic> {
    let record = leanchecker::run_leanchecker(
        toolchain,
        LEANCHECKER_IDENTITY_MODULE,
        lean_path,
        workspace_root,
        limits,
        normalizer,
    )?;
    let combined = format!("{}{}", record.stdout.trim_end(), record.stderr.trim_end());
    let observed = format!("{}\n", combined.trim_end());
    if record.exit_code == 0 || observed != LEANCHECKER_IDENTITY_OUTPUT {
        return Err(Diagnostic::new(
            code!("LLV7001"),
            format!(
                "leanchecker identity probe answered exit {} with `{}`, expected `{}`",
                record.exit_code,
                observed.trim_end(),
                LEANCHECKER_IDENTITY_OUTPUT.trim_end()
            ),
        ));
    }
    Ok(observed)
}

/// Compare a staged directory against a published one: every file
/// byte-equal, no extra or missing files on either side.
fn validate_existing(staged: &std::path::Path, published: &Utf8Path) -> Result<(), String> {
    fn files_of(root: &std::path::Path) -> BTreeMap<String, std::path::PathBuf> {
        let mut out = BTreeMap::new();
        for entry in walkdir::WalkDir::new(root).into_iter().flatten() {
            if entry.file_type().is_file() {
                if let Ok(relative) = entry.path().strip_prefix(root) {
                    out.insert(
                        relative.to_string_lossy().replace('\\', "/"),
                        entry.path().to_path_buf(),
                    );
                }
            }
        }
        out
    }
    let staged_files = files_of(staged);
    let published_files = files_of(published.as_std_path());
    for name in staged_files.keys() {
        if !published_files.contains_key(name) {
            return Err(format!("`{name}` is missing from the published set"));
        }
    }
    for name in published_files.keys() {
        if !staged_files.contains_key(name) {
            return Err(format!(
                "`{name}` is an unexplained extra file in the published set"
            ));
        }
    }
    for (name, staged_path) in &staged_files {
        // The attestation records the current run's host-bound process
        // records; content-addressing already guarantees equality of the
        // body that determines the ID, so the file must be byte-equal too.
        let published_path = &published_files[name];
        let (Ok(a), Ok(b)) = (std::fs::read(staged_path), std::fs::read(published_path)) else {
            return Err(format!("`{name}` could not be read for comparison"));
        };
        if a != b {
            return Err(format!("`{name}` differs from the published bytes"));
        }
    }
    Ok(())
}

/// Fail on any warning or unexpected output from a successful Lean process
/// (§20.2, §22.3): `accepted_stdout` is the only stdout allowed.
fn require_silent(
    record: &ChildRecord,
    stage: &str,
    accepted_stdout: bool,
) -> Result<(), Diagnostic> {
    let stdout_noise = !accepted_stdout && !record.stdout.trim().is_empty();
    if stdout_noise || !record.stderr.trim().is_empty() {
        return Err(Diagnostic::new(
            code!("LLV7006"),
            format!(
                "unexpected output during {stage}: {}{}",
                record.stdout.trim_end(),
                record.stderr.trim_end()
            ),
        ));
    }
    Ok(())
}

/// Run the complete verification pipeline (§22.1) over a rendered build.
/// The caller holds the project mutation lock for the whole run (§21.8).
#[allow(clippy::too_many_lines)]
pub fn run(
    project: &Project,
    lock: &Lock,
    checked: &CheckedProject,
    build: &RenderedBuild,
) -> Result<VerifyOutcome, LexLeanError> {
    let limits = project.config.limits;

    // Stage 4: toolchain preflight (§22.2).
    let mut toolchain: Toolchain = toolchain::preflight(&limits).map_err(fail)?;
    let toolchain_bin = toolchain.root.join("bin");

    // Stage 5: Lake workspace preflight (§10.4) and module-name conflicts
    // (§18.8, §18.9).
    workspace::preflight(project, lock).map_err(fail)?;
    let semantic_hex32: String = checked.semantic_id.to_hex()[..32].to_owned();
    let probe_name = format!("LexLeanProbe.P{semantic_hex32}");
    let audit_name = format!("LexLeanAudit.A{semantic_hex32}");
    let mut all_names: Vec<String> = build
        .modules
        .iter()
        .map(|module| module.lean_module.clone())
        .collect();
    all_names.push(probe_name.clone());
    all_names.push(audit_name.clone());
    workspace::reject_module_conflicts(project, &all_names).map_err(fail)?;

    // Every external reached by any module (§18.8): direct globals, defined
    // values, and case constructors.
    let mut externals: BTreeMap<String, crate::ir::term::ExternalConstRef> =
        checked.external_used.clone();
    for checked_module in checked.modules.values() {
        // Core-module external closure was established during linking.  Its
        // expression DAG is deliberately released after rendering so Lean,
        // rather than a duplicate Rust graph, owns the verification peak.
        if checked_module.document.core.is_none() {
            externals.extend(crate::backend::lean::document_externals(
                &checked_module.document,
                &checked.closure,
            ));
        }
    }
    let probe = crate::backend::lean::probe_module(&semantic_hex32, &externals, &checked.closure)
        .map_err(fail)?;
    debug_assert_eq!(probe.name, probe_name);

    // Stage 9 preparation: the audit module text is fixed by the build.
    let mut declaration_names: Vec<String> = Vec::new();
    for module in &build.modules {
        let document = &checked.modules[&module.module].document;
        for declaration in document.declarations() {
            declaration_names.push(format!("{}.{}", module.lean_module, declaration.lean_name));
        }
        if let Some(core) = &document.core {
            declaration_names.extend(
                core.declarations
                    .iter()
                    .map(|declaration| declaration.name.clone()),
            );
        }
    }
    declaration_names.sort();
    let generated_module_names: Vec<String> = build
        .modules
        .iter()
        .map(|module| module.lean_module.clone())
        .collect();
    let (audit_module_name, audit_text) = crate::backend::lean::audit_module(
        &semantic_hex32,
        &generated_module_names,
        &declaration_names,
    );
    debug_assert_eq!(audit_module_name, audit_name);

    // Generated-source audit before any Lean invocation (§18.2): the build
    // modules, the probe, and the audit module itself.
    for module in &build.modules {
        let is_core = checked
            .modules
            .get(&module.module)
            .is_some_and(|checked| checked.document.core.is_some());
        let audited = if is_core {
            generated_core_source_audit(&module.lean_text)
        } else {
            generated_source_audit(&module.lean_text, false)
        };
        if let Err(reason) = audited {
            return Err(fail(internal(format!(
                "`{}`: {reason}",
                module.lean_module
            ))));
        }
    }
    if let Err(reason) = generated_source_audit(&probe.text, false) {
        return Err(fail(internal(format!("probe module: {reason}"))));
    }
    if let Err(reason) = generated_source_audit(&audit_text, true) {
        return Err(fail(internal(format!("audit module: {reason}"))));
    }

    // Staging under the build root with owner-only permissions (§25.6).
    let verified_root = project
        .root
        .join(&project.config.build_root)
        .join("verified");
    std::fs::create_dir_all(verified_root.as_std_path()).map_err(|io_error| {
        fail(Diagnostic::new(
            code!("LLB6003"),
            format!("{verified_root}: {io_error}"),
        ))
    })?;
    let staging = tempfile::Builder::new()
        .prefix(".staging-")
        .tempdir_in(verified_root.as_std_path())
        .map_err(|io_error| {
            fail(Diagnostic::new(
                code!("LLB6003"),
                format!("staging: {io_error}"),
            ))
        })?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = std::fs::set_permissions(staging.path(), std::fs::Permissions::from_mode(0o700));
    }
    let staging_utf8 = Utf8PathBuf::from_path_buf(staging.path().to_path_buf())
        .map_err(|_| fail(Diagnostic::new(code!("LLS8001"), "non-UTF-8 staging path")))?;
    // The external PDF provider's isolated directory is a sibling of the
    // staging tree, never inside it (§19.7 step 4, §25.6): the provider is
    // an untrusted external program, and a program that walks out of its
    // working directory must not reach the artifacts being staged for
    // publication. Both live under the configured build root.
    let provider_root = project.root.join(&project.config.build_root).join("pdf");
    std::fs::create_dir_all(provider_root.as_std_path()).map_err(|io_error| {
        fail(Diagnostic::new(
            code!("LLB6003"),
            format!("{provider_root}: {io_error}"),
        ))
    })?;
    let workspace_root = if project.config.lean_workspace == "." {
        project.root.clone()
    } else {
        project.root.join(&project.config.lean_workspace)
    };
    let normalizer = Normalizer::new(
        &staging_utf8,
        &project.root,
        &workspace_root,
        &toolchain.root,
    );

    // Copy the platform-independent build artifacts into the verified set
    // (§22.8).
    for (relative, bytes) in &build.files {
        let renamed = if relative == "manifest.json" {
            "build-manifest.json".to_owned()
        } else {
            relative.clone()
        };
        write_staged(staging.path(), &renamed, bytes)?;
    }

    // Stage the compilation tree.
    let src_root = staging_utf8.join("lean-src");
    let olean_root = staging_utf8.join("oleans");
    std::fs::create_dir_all(olean_root.as_std_path()).map_err(|io_error| {
        fail(Diagnostic::new(
            code!("LLB6003"),
            format!("staging oleans: {io_error}"),
        ))
    })?;
    for module in &build.modules {
        let module_path = module.lean_module.replace('.', "/");
        write_staged(
            staging.path(),
            &format!("lean-src/{module_path}.lean"),
            module.lean_text.as_bytes(),
        )?;
    }
    let lean_path_env = format!("{olean_root}");
    let mut process_records: Vec<ChildRecord> = Vec::new();

    // The leanchecker identity (module documentation), before any replay:
    // the preflight's toolchain-relative path and digest line, then the
    // fixed probe's normalized answer.
    let probe_answer = leanchecker_identity(
        &toolchain,
        &lean_path_env,
        &workspace_root,
        &limits,
        &normalizer,
    )
    .map_err(fail)?;
    toolchain.leanchecker.version_output =
        format!("{}\n{probe_answer}", toolchain.leanchecker.version_output);

    // Stage 6: the external-interface probe (§18.8).
    write_staged(
        staging.path(),
        &format!("probe/{probe_name}.lean"),
        probe.text.as_bytes(),
    )?;
    let probe_source = staging_utf8
        .join("probe")
        .join(format!("{probe_name}.lean"));
    let probe_record = run_child(
        &ChildSpec {
            tool: "lean",
            module: Some(probe_name.clone()),
            program: &toolchain.lake.path,
            executable_sha256: toolchain.lean.sha256,
            argv: vec![
                "env".to_owned(),
                "lean".to_owned(),
                probe_source.to_string(),
            ],
            cwd: &workspace_root,
            extra_env: vec![("LEAN_PATH".to_owned(), lean_path_env.clone())],
            home: ChildHome::Toolchain {
                toolchain_bin: &toolchain_bin,
            },
        },
        &limits,
        &normalizer,
    )
    .map_err(fail)?;
    if probe_record.exit_code != 0 {
        // Lean writes messages to stdout under `lake env lean`; both
        // normalized streams are reported, and every failing line is
        // attributed to its entry (S11).
        let combined = format!("{}{}", probe_record.stdout, probe_record.stderr);
        let mut diagnostic = Diagnostic::new(
            code!("LLT4003"),
            format!(
                "an external-interface probe failed to elaborate: {}",
                combined.trim_end()
            ),
        );
        let mut noted: BTreeSet<String> = BTreeSet::new();
        for message in parse_lean_messages(&combined) {
            if let Some(row) = probe.entry_at_line(message.line) {
                if noted.insert(row.entry.clone()) {
                    diagnostic = diagnostic.with_note(format!(
                        "probe line {} belongs to entry `{}` (probe index {}): {}",
                        row.line, row.entry, row.index, message.message
                    ));
                }
            }
        }
        return Err(fail(diagnostic));
    }
    require_silent(&probe_record, "the external-interface probe", false).map_err(fail)?;
    write_staged(
        staging.path(),
        "probe/process.json",
        &probe_record.to_json().to_file_bytes(),
    )?;
    process_records.push(probe_record);

    // Stage 7: module elaboration in topological import order (§22.3).
    let ordered: Vec<&RenderedModule> = {
        let mut order = Vec::new();
        let mut placed: BTreeSet<&str> = BTreeSet::new();
        let mut remaining: Vec<&RenderedModule> = build.modules.iter().collect();
        while !remaining.is_empty() {
            let before = remaining.len();
            remaining.retain(|module| {
                let document = &checked.modules[&module.module].document;
                let ready = document
                    .imports
                    .iter()
                    .all(|import| placed.contains(import.as_str()));
                if ready {
                    order.push(*module);
                    placed.insert(module.module.as_str());
                    false
                } else {
                    true
                }
            });
            if remaining.len() == before {
                return Err(fail(internal("module order did not converge")));
            }
        }
        order
    };
    for module in &ordered {
        let module_path = module.lean_module.replace('.', "/");
        let source = src_root.join(format!("{module_path}.lean"));
        let olean = olean_root.join(format!("{module_path}.olean"));
        if let Some(parent) = olean.parent() {
            std::fs::create_dir_all(parent.as_std_path()).map_err(|io_error| {
                fail(Diagnostic::new(
                    code!("LLB6003"),
                    format!("staging oleans: {io_error}"),
                ))
            })?;
        }
        let record = run_child(
            &ChildSpec {
                tool: "lean",
                module: Some(module.lean_module.clone()),
                program: &toolchain.lake.path,
                executable_sha256: toolchain.lean.sha256,
                argv: vec![
                    "env".to_owned(),
                    "lean".to_owned(),
                    "-o".to_owned(),
                    olean.to_string(),
                    source.to_string(),
                ],
                cwd: &workspace_root,
                extra_env: vec![("LEAN_PATH".to_owned(), lean_path_env.clone())],
                home: ChildHome::Toolchain {
                    toolchain_bin: &toolchain_bin,
                },
            },
            &limits,
            &normalizer,
        )
        .map_err(fail)?;
        if record.exit_code != 0 {
            // Lean reports compile errors on stdout under `lake env lean`;
            // remap over both streams (§20.4).
            let combined = format!("{}\n{}", record.stdout, record.stderr);
            return Err(LexLeanError::from_diagnostics(remap_lean_output(
                checked,
                build,
                &module.lean_module,
                &combined,
                LeanOutcome::Rejected,
            )));
        }
        // Any warning or unknown informational message fails verification
        // (§20.2, §22.3), remapped to its source span exactly like an error.
        if !record.stdout.trim().is_empty() || !record.stderr.trim().is_empty() {
            let combined = format!("{}\n{}", record.stdout, record.stderr);
            return Err(LexLeanError::from_diagnostics(remap_lean_output(
                checked,
                build,
                &module.lean_module,
                &combined,
                LeanOutcome::Noisy,
            )));
        }
        if !olean.as_std_path().is_file() {
            return Err(fail(Diagnostic::new(
                code!("LLV7002"),
                format!("`{}` produced no olean", module.lean_module),
            )));
        }
        write_staged(
            staging.path(),
            &format!("process/lean/{}.json", module.lean_module),
            &record.to_json().to_file_bytes(),
        )?;
        process_records.push(record);
    }

    // Stage 8: separate-process leanchecker replay per module, sorted
    // (§22.4).
    let mut sorted_modules: Vec<&RenderedModule> = build.modules.iter().collect();
    sorted_modules.sort_by(|a, b| a.lean_module.cmp(&b.lean_module));
    for module in &sorted_modules {
        let record = leanchecker::replay_module(
            &toolchain,
            &module.lean_module,
            &lean_path_env,
            &workspace_root,
            &limits,
            &normalizer,
        )
        // A replay failure is about this module, so it points at the
        // module's own source rather than at the project manifest (§20.1).
        .map_err(|diagnostic| fail(diagnostic.with_span(source_span(checked, module, (0, 0)))))?;
        write_staged(
            staging.path(),
            &format!("process/leanchecker/{}.json", module.lean_module),
            &record.to_json().to_file_bytes(),
        )?;
        process_records.push(record);
    }

    // Stage 9–10: the audit module and exact output parsing (§18.9, §22.5).
    write_staged(
        staging.path(),
        &format!("audit/{audit_name}.lean"),
        audit_text.as_bytes(),
    )?;
    let audit_source = staging_utf8
        .join("audit")
        .join(format!("{audit_name}.lean"));
    let audit_record = run_child(
        &ChildSpec {
            tool: "lean",
            module: Some(audit_name.clone()),
            program: &toolchain.lake.path,
            executable_sha256: toolchain.lean.sha256,
            argv: vec![
                "env".to_owned(),
                "lean".to_owned(),
                audit_source.to_string(),
            ],
            cwd: &workspace_root,
            extra_env: vec![("LEAN_PATH".to_owned(), lean_path_env.clone())],
            home: ChildHome::Toolchain {
                toolchain_bin: &toolchain_bin,
            },
        },
        &limits,
        &normalizer,
    )
    .map_err(fail)?;
    if audit_record.exit_code != 0 {
        return Err(fail(Diagnostic::new(
            code!("LLV7004"),
            format!(
                "the axiom audit failed: {}{}",
                audit_record.stdout.trim_end(),
                audit_record.stderr.trim_end()
            ),
        )));
    }
    // The audit's stdout is exactly the `#print axioms` records (checked by
    // the parser); its stderr must be empty (§20.2).
    require_silent(&audit_record, "the axiom audit", true).map_err(fail)?;
    write_staged(
        staging.path(),
        "audit/output.txt",
        audit_record.stdout.as_bytes(),
    )?;
    write_staged(
        staging.path(),
        "audit/process.json",
        &audit_record.to_json().to_file_bytes(),
    )?;
    let observed = axiom::parse_audit_output(&audit_record.stdout, &declaration_names)
        .map_err(|failure| fail(audit_diagnostic(checked, build, failure)))?;
    process_records.push(audit_record);

    // Stage 11: per-declaration policy enforcement (§22.6).
    let mut declaration_rows: Vec<Json> = Vec::new();
    for module in &build.modules {
        let document = &checked.modules[&module.module].document;
        for declaration in document.declarations() {
            let full_name = format!("{}.{}", module.lean_module, declaration.lean_name);
            let observed_set = observed.get(&full_name).cloned().unwrap_or_default();
            if !declaration.policy.permits(&observed_set) {
                let mut diagnostic = Diagnostic::new(
                    code!("LLV7005"),
                    format!(
                        "`{full_name}` violates its {} axiom policy: observed [{}]",
                        declaration.policy.kind(),
                        observed_set.join(", ")
                    ),
                );
                if let Some(span) =
                    declaration_span(checked, module, &document.name, &declaration.component)
                {
                    diagnostic = diagnostic.with_span(span);
                }
                return Err(fail(diagnostic));
            }
            declaration_rows.push(Json::object(vec![
                ("name", Json::Str(full_name)),
                (
                    "policy",
                    Json::object(vec![
                        ("kind", Json::Str(declaration.policy.kind().to_owned())),
                        (
                            "axioms",
                            Json::Arr(
                                declaration
                                    .policy
                                    .axioms()
                                    .iter()
                                    .cloned()
                                    .map(Json::Str)
                                    .collect(),
                            ),
                        ),
                    ]),
                ),
                (
                    "observed",
                    Json::Arr(observed_set.into_iter().map(Json::Str).collect()),
                ),
                ("result", Json::Str("ok".to_owned())),
            ]));
        }
        if let Some(core) = &document.core {
            for declaration in &core.declarations {
                let observed_set = observed.get(&declaration.name).cloned().unwrap_or_default();
                if !declaration.policy.permits(&observed_set) {
                    return Err(fail(Diagnostic::new(
                        code!("LLV7005"),
                        format!(
                            "`{}` violates its {} axiom policy: observed [{}]",
                            declaration.name,
                            declaration.policy.kind(),
                            observed_set.join(", ")
                        ),
                    )));
                }
                declaration_rows.push(Json::object(vec![
                    ("name", Json::Str(declaration.name.clone())),
                    (
                        "policy",
                        Json::object(vec![
                            ("kind", Json::Str(declaration.policy.kind().to_owned())),
                            (
                                "axioms",
                                Json::Arr(
                                    declaration
                                        .policy
                                        .axioms()
                                        .iter()
                                        .cloned()
                                        .map(Json::Str)
                                        .collect(),
                                ),
                            ),
                        ]),
                    ),
                    (
                        "observed",
                        Json::Arr(observed_set.into_iter().map(Json::Str).collect()),
                    ),
                    ("result", Json::Str("ok".to_owned())),
                ]));
            }
        }
    }

    // Stage 12: optional configured PDF rendering (§19.7): one row and two
    // process records per module.
    let mut pdf_rows: Vec<Json> = Vec::new();
    if let Some(provider) = &project.config.pdf {
        for module in &build.modules {
            let result = crate::backend::pdf::run_provider(
                project,
                provider,
                module.tex_text.as_bytes(),
                &module.lean_module,
                &provider_root,
                &normalizer,
            )
            .map_err(fail)?;
            write_staged(
                staging.path(),
                &format!("pdf/{}.pdf", module.lean_module),
                &result.pdf_bytes,
            )?;
            let version_record = result.version;
            let compile_record = result.compile;
            write_staged(
                staging.path(),
                &format!("pdf/{}.version.json", module.lean_module),
                &version_record.to_json().to_file_bytes(),
            )?;
            write_staged(
                staging.path(),
                &format!("pdf/{}.compile.json", module.lean_module),
                &compile_record.to_json().to_file_bytes(),
            )?;
            pdf_rows.push(Json::object(vec![
                ("module", Json::Str(module.lean_module.clone())),
                ("recipe_id", Json::Str(result.recipe_id.to_hex())),
                ("pdf_sha256", Json::Str(result.pdf_sha256.to_hex())),
                ("byte_length", Json::from_usize(result.pdf_bytes.len())),
                ("version", version_record.to_json()),
                ("compile", compile_record.to_json()),
            ]));
            process_records.push(version_record);
            process_records.push(compile_record);
        }
    }

    // Stage 13: no unexpected absolute paths in successful output (§22.7),
    // over every process record.
    for record in &process_records {
        if normalizer.has_unexpected_absolute_path(&record.stdout)
            || normalizer.has_unexpected_absolute_path(&record.stderr)
        {
            return Err(fail(Diagnostic::new(
                code!("LLV7006"),
                format!(
                    "unexpected absolute path in the output of `{}`{}",
                    record.tool,
                    record
                        .module
                        .as_ref()
                        .map_or_else(String::new, |module| format!(" for `{module}`"))
                ),
            )));
        }
    }

    // Remove the compilation scratch tree; the fixed §22.8 artifact set
    // keeps exactly `oleans/*.olean` (the module-system `.olean.private`,
    // `.olean.server`, and `.ir` intermediates are not part of the set and
    // are removed once every consumer — later modules, the replay, and the
    // audit — has run).
    let _ = std::fs::remove_dir_all(src_root.as_std_path());
    for entry in walkdir::WalkDir::new(olean_root.as_std_path())
        .into_iter()
        .flatten()
    {
        if entry.file_type().is_file()
            && entry
                .path()
                .extension()
                .is_none_or(|extension| extension != "olean")
        {
            std::fs::remove_file(entry.path()).map_err(|io_error| {
                fail(Diagnostic::new(
                    code!("LLB6003"),
                    format!("removing {}: {io_error}", entry.path().display()),
                ))
            })?;
        }
    }

    // Copy oleans into the verified set and hash them.
    let mut olean_rows: Vec<Json> = Vec::new();
    for module in &build.modules {
        let module_path = module.lean_module.replace('.', "/");
        let olean = olean_root.join(format!("{module_path}.olean"));
        let bytes = std::fs::read(olean.as_std_path()).map_err(|io_error| {
            fail(Diagnostic::new(
                code!("LLV7002"),
                format!("{olean}: {io_error}"),
            ))
        })?;
        olean_rows.push(Json::object(vec![
            ("module", Json::Str(module.lean_module.clone())),
            ("byte_length", Json::from_usize(bytes.len())),
            ("sha256", Json::Str(Sha256Digest::of(&bytes).to_hex())),
        ]));
    }

    // Stage 14: the attestation (§22.9). No timestamp is hashed. The
    // running executable must be readable to be recorded; nothing is
    // fabricated in its place.
    let lexlean_executable_sha256 = std::env::current_exe()
        .and_then(std::fs::read)
        .map(|bytes| Sha256Digest::of(&bytes))
        .map_err(|io_error| {
            fail(internal(format!(
                "reading the running executable: {io_error}"
            )))
        })?;
    let tool_json = |tool: &toolchain::Tool| {
        Json::object(vec![
            ("version_output", Json::Str(tool.version_output.clone())),
            ("executable_sha256", Json::Str(tool.sha256.to_hex())),
        ])
    };
    let mut body_fields = vec![
        ("spec", Json::Str("lexlean/attestation/1".to_owned())),
        ("status", Json::Str("verified".to_owned())),
        ("semantic_id", Json::Str(checked.semantic_id.to_hex())),
        ("source_id", Json::Str(checked.source_id.to_hex())),
        ("build_id", Json::Str(build.build_id.to_hex())),
        (
            "host",
            Json::object(vec![
                ("os", Json::Str(std::env::consts::OS.to_owned())),
                ("arch", Json::Str(std::env::consts::ARCH.to_owned())),
            ]),
        ),
        (
            "lexlean",
            Json::object(vec![
                ("version", Json::Str(crate::COMPILER_VERSION.to_owned())),
                (
                    "compiler_semantics",
                    Json::Str(crate::compiler_semantics_id().to_hex()),
                ),
                (
                    "executable_sha256",
                    Json::Str(lexlean_executable_sha256.to_hex()),
                ),
            ]),
        ),
        (
            "toolchain",
            Json::object(vec![
                ("lean", tool_json(&toolchain.lean)),
                ("lake", tool_json(&toolchain.lake)),
                ("leanchecker", tool_json(&toolchain.leanchecker)),
            ]),
        ),
        (
            "lake_workspace",
            Json::Arr(
                lock.workspace_files
                    .iter()
                    .map(|(path, sha256)| {
                        Json::object(vec![
                            ("path", Json::Str(path.clone())),
                            ("sha256", Json::Str(sha256.to_hex())),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "build_manifest",
            Json::object(vec![
                ("byte_length", Json::from_usize(build.manifest_bytes.len())),
                (
                    "sha256",
                    Json::Str(Sha256Digest::of(&build.manifest_bytes).to_hex()),
                ),
            ]),
        ),
        ("oleans", Json::Arr(olean_rows)),
        (
            "processes",
            Json::Arr(process_records.iter().map(ChildRecord::to_json).collect()),
        ),
        ("declarations", Json::Arr(declaration_rows)),
    ];
    if !pdf_rows.is_empty() {
        body_fields.push(("pdf", Json::Arr(pdf_rows)));
    }
    let body = Json::object(body_fields);
    let this_attestation_id = attestation_id(&body.to_canonical_string());
    let full = match body {
        Json::Obj(mut object) => {
            object.insert(
                "attestation_id".to_owned(),
                Json::Str(this_attestation_id.to_hex()),
            );
            Json::Obj(object)
        }
        other => other,
    };
    write_staged(staging.path(), "attestation.json", &full.to_file_bytes())?;

    // Stage 15: atomic publication (§21.8).
    let target = verified_root.join(this_attestation_id.to_hex());
    if target.as_std_path().exists() {
        // A repeated verification of identical content reuses the
        // published set only after every staged file validates against it
        // (§21.8); anything else refuses to overwrite unexplained bytes.
        return match validate_existing(staging.path(), &target) {
            Ok(()) => Ok(VerifyOutcome {
                attestation_id: this_attestation_id,
                root: target,
            }),
            Err(reason) => Err(fail(Diagnostic::new(
                code!("LLB6003"),
                format!(
                    "existing verified directory {target} does not validate against this run: {reason}; refusing to overwrite unexplained bytes"
                ),
            ))),
        };
    }
    let staged = staging.keep();
    std::fs::rename(&staged, target.as_std_path()).map_err(|io_error| {
        let _ = std::fs::remove_dir_all(&staged);
        fail(Diagnostic::new(
            code!("LLB6003"),
            format!("publishing {target}: {io_error}"),
        ))
    })?;
    crate::artifact::fsync_dir(verified_root.as_std_path());
    Ok(VerifyOutcome {
        attestation_id: this_attestation_id,
        root: target,
    })
}

/// A helper for tests: the reserved probe and audit module names for a
/// semantic ID (§18.8, §18.9).
#[must_use]
pub fn reserved_module_names(semantic_id: Sha256Digest) -> (String, String) {
    let hex32: String = semantic_id.to_hex()[..32].to_owned();
    (
        format!("LexLeanProbe.P{hex32}"),
        format!("LexLeanAudit.A{hex32}"),
    )
}
