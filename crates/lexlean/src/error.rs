//! The closed public failure model (SPEC.md §24.5, §23.6).
//!
//! Every public function returns only [`LexLeanError`]; its [`ErrorClass`]
//! maps exactly to the CLI exit codes 1, 2, 3, 4, and 70. Malformed user
//! input never panics (I14): everything user-controlled flows into
//! diagnostics with registered codes.

use crate::diagnostic::Diagnostic;

/// The five sanctioned failure classes (SPEC.md §24.5).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ErrorClass {
    /// Source, glossary, grammar, semantic, Lean, proof, or axiom-policy
    /// failure. Exit code 1.
    Language,
    /// CLI misuse, project-config error, lock-schema error, or invalid
    /// selection. Exit code 2.
    CliOrConfiguration,
    /// Missing or mismatched toolchain, Lake workspace, executable, or
    /// environment. Exit code 3.
    Environment,
    /// Security-policy or explicit resource-limit violation. Exit code 4.
    SecurityOrLimit,
    /// Internal invariant or software failure. Exit code 70.
    Internal,
}

impl ErrorClass {
    /// The exact documented CLI exit code (SPEC.md §23.6).
    #[must_use]
    pub const fn exit_code(self) -> i32 {
        match self {
            Self::Language => 1,
            Self::CliOrConfiguration => 2,
            Self::Environment => 3,
            Self::SecurityOrLimit => 4,
            Self::Internal => 70,
        }
    }

    /// The class token used by `model/errors.toml`.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Language => "language",
            Self::CliOrConfiguration => "cli-configuration",
            Self::Environment => "environment",
            Self::SecurityOrLimit => "security-limit",
            Self::Internal => "internal",
        }
    }
}

/// The one public error type (SPEC.md §24.5).
#[derive(Debug)]
pub struct LexLeanError {
    /// The sanctioned failure class; decides the exit code.
    pub class: ErrorClass,
    /// Every diagnostic collected before the failure, in canonical order.
    pub diagnostics: Vec<Diagnostic>,
    /// An optional underlying host error, never a substitute for a
    /// registered diagnostic.
    pub source: Option<Box<dyn std::error::Error + Send + Sync>>,
}

impl LexLeanError {
    /// A failure carrying one diagnostic; the class comes from the
    /// diagnostic's registered code.
    #[must_use]
    pub fn from_diagnostic(diagnostic: Diagnostic) -> Self {
        Self {
            class: diagnostic.code.class(),
            diagnostics: vec![diagnostic],
            source: None,
        }
    }

    /// A failure carrying many diagnostics; the class is the most severe
    /// (highest exit code wins, so an internal failure is never downgraded).
    #[must_use]
    pub fn from_diagnostics(mut diagnostics: Vec<Diagnostic>) -> Self {
        crate::diagnostic::sort_canonical(&mut diagnostics);
        let class = diagnostics
            .iter()
            .map(|d| d.code.class())
            .max_by_key(|c| c.exit_code())
            .unwrap_or(ErrorClass::Internal);
        Self {
            class,
            diagnostics,
            source: None,
        }
    }

    /// Attach a host-level cause.
    #[must_use]
    pub fn with_source(mut self, source: Box<dyn std::error::Error + Send + Sync>) -> Self {
        self.source = Some(source);
        self
    }
}

impl std::fmt::Display for LexLeanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.diagnostics.as_slice() {
            [] => write!(f, "{} failure with no diagnostic", self.class.as_str()),
            [first, rest @ ..] => {
                write!(f, "{}: {}", first.code.as_str(), first.message)?;
                if !rest.is_empty() {
                    write!(f, " (+{} more)", rest.len())?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for LexLeanError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source
            .as_deref()
            .map(|e| e as &(dyn std::error::Error + 'static))
    }
}
