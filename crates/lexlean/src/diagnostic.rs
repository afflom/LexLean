//! Canonical diagnostics (SPEC.md §20.1, §26).
//!
//! Every user-visible failure carries a registered code (I14). Source
//! constructs codes only through the [`code!`](crate::code) macro, whose
//! argument is a compile-time string literal validated by
//! [`DiagnosticCode::validate`]; `cargo xtask validate-model` cross-checks
//! every literal against `model/errors.toml`.

use std::collections::BTreeMap;

use crate::artifact::canonical_json::Json;
use crate::error::ErrorClass;

/// A registered diagnostic code, `LL<letter><four digits>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct DiagnosticCode(&'static str);

impl DiagnosticCode {
    /// Compile-time shape check for the [`code!`](crate::code) macro. Panics
    /// in `const` evaluation on a malformed literal, so an invalid code is a
    /// build failure rather than a runtime surprise.
    #[must_use]
    pub const fn validate(code: &'static str) -> &'static str {
        let bytes = code.as_bytes();
        assert!(bytes.len() == 7, "a diagnostic code is exactly 7 bytes");
        assert!(
            bytes[0] == b'L' && bytes[1] == b'L',
            "a diagnostic code starts with LL"
        );
        assert!(
            matches!(
                bytes[2],
                b'C' | b'L' | b'P' | b'R' | b'T' | b'F' | b'B' | b'V' | b'S' | b'I'
            ),
            "unknown diagnostic range letter"
        );
        let mut i = 3;
        while i < 7 {
            assert!(bytes[i].is_ascii_digit(), "code digits must be ASCII");
            i += 1;
        }
        code
    }

    /// Construct from a literal already validated by [`Self::validate`].
    /// Only the [`code!`](crate::code) macro constructs codes; this is an
    /// unstable implementation detail of that macro (§26.1).
    #[doc(hidden)]
    #[must_use]
    pub const fn from_validated(code: &'static str) -> Self {
        Self(code)
    }

    /// The code text, e.g. `LLL1004`.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        self.0
    }

    /// The sanctioned failure class for this code. This mapping is asserted
    /// equal to `model/errors.toml` by the conformance suite, so the registry
    /// stays the single source (R1).
    #[must_use]
    pub fn class(self) -> ErrorClass {
        match self.0 {
            // §23.6 places external-tool and toolchain mismatches in the
            // environment class even though their ranges are language-family.
            "LLB6004" | "LLV7001" | "LLV7007" | "LLV7008" | "LLV7009" | "LLV7010" => {
                ErrorClass::Environment
            }
            _ => match self.0.as_bytes()[2] {
                b'C' => ErrorClass::CliOrConfiguration,
                b'S' => ErrorClass::SecurityOrLimit,
                b'I' => ErrorClass::Internal,
                _ => ErrorClass::Language,
            },
        }
    }
}

/// Construct a [`DiagnosticCode`](crate::diagnostic::DiagnosticCode) from a
/// compile-time literal (SPEC.md §26.1).
#[macro_export]
macro_rules! code {
    ($code:literal) => {{
        const VALIDATED: &str = $crate::diagnostic::DiagnosticCode::validate($code);
        $crate::diagnostic::DiagnosticCode::from_validated(VALIDATED)
    }};
}

/// A half-open source span with one-based line/column display coordinates
/// (SPEC.md §20.1). Columns count Unicode scalar values after normalization.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    /// Project-relative path of the file.
    pub path: String,
    /// Zero-based half-open UTF-8 byte offsets.
    pub byte_start: usize,
    /// End byte offset, exclusive.
    pub byte_end: usize,
    /// One-based start line.
    pub line_start: usize,
    /// One-based start column in scalar values.
    pub column_start: usize,
    /// One-based end line.
    pub line_end: usize,
    /// One-based end column in scalar values.
    pub column_end: usize,
}

impl Span {
    /// A degenerate span at the start of a file, for failures that concern a
    /// file as a whole rather than a range inside it.
    #[must_use]
    pub fn whole_file(path: &str) -> Self {
        Self {
            path: path.to_owned(),
            byte_start: 0,
            byte_end: 0,
            line_start: 1,
            column_start: 1,
            line_end: 1,
            column_end: 1,
        }
    }

    fn to_json(&self) -> Json {
        let mut object = BTreeMap::new();
        object.insert("path".to_owned(), Json::Str(self.path.clone()));
        object.insert("byte_start".to_owned(), Json::from_usize(self.byte_start));
        object.insert("byte_end".to_owned(), Json::from_usize(self.byte_end));
        object.insert("line_start".to_owned(), Json::from_usize(self.line_start));
        object.insert(
            "column_start".to_owned(),
            Json::from_usize(self.column_start),
        );
        object.insert("line_end".to_owned(), Json::from_usize(self.line_end));
        object.insert("column_end".to_owned(), Json::from_usize(self.column_end));
        Json::Obj(object)
    }
}

/// A secondary labeled span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label {
    /// What this span shows.
    pub message: String,
    /// Where.
    pub span: Span,
}

/// An attached note, optionally located (SPEC.md §20.4 keeps generated Lean
/// locations as notes).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Note {
    /// The note text.
    pub message: String,
    /// An optional location.
    pub span: Option<Span>,
}

/// One canonical diagnostic (SPEC.md §20.1). Severity is always `error`;
/// language 1.0 has no recoverable compiler warning category (§20.2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    /// The registered code.
    pub code: DiagnosticCode,
    /// The one-line message.
    pub message: String,
    /// The primary location, absent only for failures with no file at all.
    pub primary: Option<Span>,
    /// Secondary labeled spans.
    pub labels: Vec<Label>,
    /// Attached notes.
    pub notes: Vec<Note>,
    /// Fix-it style help lines.
    pub help: Vec<String>,
    /// Underlying causes, innermost last.
    pub causes: Vec<String>,
}

impl Diagnostic {
    /// A diagnostic with no location.
    #[must_use]
    pub fn new(code: DiagnosticCode, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            primary: None,
            labels: Vec::new(),
            notes: Vec::new(),
            help: Vec::new(),
            causes: Vec::new(),
        }
    }

    /// Attach the primary span.
    #[must_use]
    pub fn with_span(mut self, span: Span) -> Self {
        self.primary = Some(span);
        self
    }

    /// Attach a labeled secondary span.
    #[must_use]
    pub fn with_label(mut self, message: impl Into<String>, span: Span) -> Self {
        self.labels.push(Label {
            message: message.into(),
            span,
        });
        self
    }

    /// Attach an unlocated note.
    #[must_use]
    pub fn with_note(mut self, message: impl Into<String>) -> Self {
        self.notes.push(Note {
            message: message.into(),
            span: None,
        });
        self
    }

    /// Attach a located note.
    #[must_use]
    pub fn with_located_note(mut self, message: impl Into<String>, span: Span) -> Self {
        self.notes.push(Note {
            message: message.into(),
            span: Some(span),
        });
        self
    }

    /// Attach a help line.
    #[must_use]
    pub fn with_help(mut self, message: impl Into<String>) -> Self {
        self.help.push(message.into());
        self
    }

    /// Attach a cause line.
    #[must_use]
    pub fn with_cause(mut self, message: impl Into<String>) -> Self {
        self.causes.push(message.into());
        self
    }

    /// The canonical JSON object (SPEC.md §20.1).
    #[must_use]
    pub fn to_json(&self) -> Json {
        let mut object = BTreeMap::new();
        object.insert(
            "spec".to_owned(),
            Json::Str("lexlean/diagnostic/1".to_owned()),
        );
        object.insert("code".to_owned(), Json::Str(self.code.as_str().to_owned()));
        object.insert("severity".to_owned(), Json::Str("error".to_owned()));
        object.insert("message".to_owned(), Json::Str(self.message.clone()));
        if let Some(primary) = &self.primary {
            object.insert("primary".to_owned(), primary.to_json());
        }
        object.insert(
            "labels".to_owned(),
            Json::Arr(
                self.labels
                    .iter()
                    .map(|label| {
                        let mut o = BTreeMap::new();
                        o.insert("message".to_owned(), Json::Str(label.message.clone()));
                        o.insert("span".to_owned(), label.span.to_json());
                        Json::Obj(o)
                    })
                    .collect(),
            ),
        );
        object.insert(
            "notes".to_owned(),
            Json::Arr(
                self.notes
                    .iter()
                    .map(|note| {
                        let mut o = BTreeMap::new();
                        o.insert("message".to_owned(), Json::Str(note.message.clone()));
                        if let Some(span) = &note.span {
                            o.insert("span".to_owned(), span.to_json());
                        }
                        Json::Obj(o)
                    })
                    .collect(),
            ),
        );
        object.insert(
            "help".to_owned(),
            Json::Arr(self.help.iter().cloned().map(Json::Str).collect()),
        );
        object.insert(
            "causes".to_owned(),
            Json::Arr(self.causes.iter().cloned().map(Json::Str).collect()),
        );
        Json::Obj(object)
    }
}

/// Sort diagnostics canonically (SPEC.md §20.1): project-relative path, byte
/// start, severity, code, message. Severity is constant in language 1.0, so
/// it never differentiates.
pub fn sort_canonical(diagnostics: &mut [Diagnostic]) {
    diagnostics.sort_by(|a, b| {
        let key = |d: &Diagnostic| {
            (
                d.primary
                    .as_ref()
                    .map(|s| s.path.clone())
                    .unwrap_or_default(),
                d.primary.as_ref().map_or(0, |s| s.byte_start),
                d.code,
                d.message.clone(),
            )
        };
        key(a).cmp(&key(b))
    });
}
