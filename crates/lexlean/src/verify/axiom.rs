//! The exact axiom-output parser (SPEC.md §22.5): only the pinned Lean
//! 4.32.1 payload forms are accepted; missing, duplicate, extra, or
//! malformed records are rejected.

use std::collections::BTreeMap;

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::lexicon::entry::is_lean_name;

fn malformed(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLV7004"), message)
}

/// Parse one payload line, already stripped of its envelope: exactly
/// `'<name>' does not depend on any axioms` or
/// `'<name>' depends on axioms: [<comma-separated Lean names>]`.
fn parse_payload(payload: &str) -> Result<(String, Vec<String>), Diagnostic> {
    let rest = payload
        .strip_prefix('\'')
        .ok_or_else(|| malformed(format!("unrecognized axiom payload: {payload}")))?;
    let (name, tail) = rest
        .split_once('\'')
        .ok_or_else(|| malformed(format!("unrecognized axiom payload: {payload}")))?;
    if !is_lean_name(name) {
        return Err(malformed(format!("`{name}` is not a Lean name")));
    }
    if tail == " does not depend on any axioms" {
        return Ok((name.to_owned(), Vec::new()));
    }
    let list = tail
        .strip_prefix(" depends on axioms: [")
        .and_then(|inner| inner.strip_suffix(']'))
        .ok_or_else(|| malformed(format!("unrecognized axiom payload: {payload}")))?;
    let mut axioms = Vec::new();
    for piece in list.split(',') {
        let axiom = piece.trim();
        if !is_lean_name(axiom) {
            return Err(malformed(format!("`{axiom}` is not a Lean name")));
        }
        if axioms.contains(&axiom.to_owned()) {
            return Err(malformed(format!("duplicate axiom name `{axiom}`")));
        }
        axioms.push(axiom.to_owned());
    }
    if axioms.is_empty() {
        return Err(malformed("an axiom list cannot be empty"));
    }
    axioms.sort();
    Ok((name.to_owned(), axioms))
}

/// Strip the optional Lean information envelope from one audit line
/// (§22.5). Lean 4.32.1's command-line driver prints an informational
/// message bare (`Lean.SerialMessage.toString` adds a location only to
/// warnings and errors), so the payload usually stands alone; the two
/// envelope shapes Lean itself produces for information messages are the
/// bare severity label `info: ` (`#guard_msgs`) and the located form
/// `path:line:col[-line:col]: info: ` (`Lean.mkErrorStringWithPos` with the
/// `information` severity spelled `info`). Nothing else is an envelope: a
/// `warning:` or `error:` label is not information and fails the audit.
fn strip_envelope(line: &str) -> Option<&str> {
    if line.starts_with('\'') {
        return Some(line);
    }
    let label = "info: ";
    if let Some(payload) = line.strip_prefix(label) {
        return Some(payload);
    }
    // `path:line:col[-line:col]: info: payload`: the location fields must
    // be numeric and the label must follow immediately.
    let mut parts = line.splitn(4, ':');
    let _path = parts.next()?;
    let line_field = parts.next()?;
    let column_field = parts.next()?;
    let rest = parts.next()?;
    line_field.trim().parse::<usize>().ok()?;
    let rest = match column_field.split_once('-') {
        Some((column, end_line)) => {
            column.trim().parse::<usize>().ok()?;
            end_line.trim().parse::<usize>().ok()?;
            let (end_column, remainder) = rest.split_once(':')?;
            end_column.trim().parse::<usize>().ok()?;
            remainder
        }
        None => {
            column_field.trim().parse::<usize>().ok()?;
            rest
        }
    };
    rest.strip_prefix(' ')?.strip_prefix(label)
}

/// Parse the complete normalized audit output against the expected
/// declaration names, in their sorted command order (§18.9, §22.5).
/// Returns the observed set per declaration, sorted and deduplicated.
pub fn parse_audit_output(
    stdout: &str,
    expected: &[String],
) -> Result<BTreeMap<String, Vec<String>>, Diagnostic> {
    let mut records: Vec<(String, Vec<String>)> = Vec::new();
    for line in stdout.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        let payload = strip_envelope(trimmed)
            .ok_or_else(|| malformed(format!("unrecognized audit line: {trimmed}")))?;
        records.push(parse_payload(payload.trim_end())?);
    }
    if records.len() != expected.len() {
        return Err(malformed(format!(
            "expected {} audit records, found {}",
            expected.len(),
            records.len()
        )));
    }
    let mut observed = BTreeMap::new();
    for (record, expected_name) in records.into_iter().zip(expected) {
        if record.0 != *expected_name {
            return Err(malformed(format!(
                "expected a record for `{expected_name}`, found `{}`",
                record.0
            )));
        }
        if observed.insert(record.0.clone(), record.1).is_some() {
            return Err(malformed(format!("duplicate record for `{}`", record.0)));
        }
    }
    Ok(observed)
}
