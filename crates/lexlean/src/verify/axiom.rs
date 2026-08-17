//! The exact axiom-output parser (SPEC.md §22.5): only the pinned Lean
//! 4.32.1 payload forms are accepted; missing, duplicate, extra, or
//! malformed records are rejected.
//!
//! A record is not a line. Lean 4.32.1 renders `#print axioms` through its
//! pretty-printer at the default format width of 120 columns, so a
//! declaration whose record is wider has its axiom list broken across
//! indented continuation lines --- the shipped propositional-logic example
//! already prints at 103 columns. The parser therefore reassembles each
//! record before applying the payload grammar; the committed vectors under
//! `tests/golden/axiom-parser/` include both shapes, captured from the
//! pinned toolchain.

use std::collections::BTreeMap;

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::lexicon::entry::is_lean_name;

/// One rejection of the audit output (SPEC.md §22.5), with the expected
/// declaration it is about when the parser can attribute it to exactly
/// one. The caller anchors the diagnostic at that declaration's source
/// span (§20.1: the primary location is the thing that failed); a
/// rejection about the stream as a whole carries none.
#[derive(Debug)]
pub struct AuditFailure {
    /// The registered diagnostic.
    pub diagnostic: Diagnostic,
    /// The expected declaration's full Lean name, when known.
    pub declaration: Option<String>,
}

impl AuditFailure {
    /// Name the declaration this failure is about.
    #[must_use]
    fn about(mut self, declaration: Option<&String>) -> Self {
        self.declaration = declaration.cloned();
        self
    }
}

fn malformed(message: impl Into<String>) -> AuditFailure {
    AuditFailure {
        diagnostic: Diagnostic::new(code!("LLV7004"), message),
        declaration: None,
    }
}

/// Does a payload end where one of §22.5's two forms ends? The pinned
/// toolchain pretty-prints the axiom list as its one `Format` group, so a
/// record breaks only inside the brackets: the closing bracket and the
/// no-axioms sentence are the only two terminators, and the
/// `does not depend on any axioms` form therefore never wraps.
fn payload_terminates(payload: &str) -> bool {
    payload.ends_with(']') || payload.ends_with(" does not depend on any axioms")
}

/// Parse one payload line, already stripped of its envelope: exactly
/// `'<name>' does not depend on any axioms` or
/// `'<name>' depends on axioms: [<comma-separated Lean names>]`.
fn parse_payload(payload: &str) -> Result<(String, Vec<String>), AuditFailure> {
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

/// Parse the complete normalized audit output against the expected
/// declaration names, in their sorted command order (§18.9, §22.5).
/// Returns the observed set per declaration, sorted and deduplicated.
pub fn parse_audit_output(
    stdout: &str,
    expected: &[String],
) -> Result<BTreeMap<String, Vec<String>>, AuditFailure> {
    let mut records: Vec<(String, Vec<String>)> = Vec::new();
    let mut lines = stdout.lines();
    while let Some(line) = lines.next() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        // The record under construction is the one expected at this
        // position, so a rejection below names the declaration whose
        // record the audit failed to produce.
        let about = expected.get(records.len());
        // An optional Lean location/information envelope precedes the
        // quoted payload; everything before the first quote is envelope,
        // and an envelope must not itself contain a quote.
        let Some(quote_at) = trimmed.find('\'') else {
            return Err(malformed(format!("unrecognized audit line: {trimmed}")).about(about));
        };
        let envelope = &trimmed[..quote_at];
        if !envelope.is_empty() {
            let plausible =
                envelope.ends_with(": ") || envelope.ends_with(':') || envelope.ends_with(' ');
            if !plausible {
                return Err(malformed(format!("unrecognized audit line: {trimmed}")).about(about));
            }
        }
        // One record, not one line: the pinned toolchain breaks a long
        // axiom list at its format width (120 columns), emitting the tail
        // as indented continuation lines. Reassemble the record before
        // parsing, joining with the single space the unwrapped form
        // spells, so exactly one payload grammar reads both shapes. A
        // continuation may not open a new record and the stream may not
        // end mid-record; either is a malformed audit output.
        let mut payload = trimmed[quote_at..].trim_end().to_owned();
        while !payload_terminates(&payload) {
            let continuation = lines
                .next()
                .map(str::trim)
                .filter(|continuation| !continuation.is_empty() && !continuation.contains('\''));
            let Some(continuation) = continuation else {
                return Err(
                    malformed(format!("unterminated axiom payload: {payload}")).about(about)
                );
            };
            payload.push(' ');
            payload.push_str(continuation);
        }
        records.push(parse_payload(&payload).map_err(|failure| failure.about(about))?);
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
            ))
            .about(Some(expected_name)));
        }
        if observed.insert(record.0.clone(), record.1).is_some() {
            return Err(malformed(format!("duplicate record for `{}`", record.0))
                .about(Some(expected_name)));
        }
    }
    Ok(observed)
}
