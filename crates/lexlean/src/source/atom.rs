//! Primitive atoms (SPEC.md §12.2).

/// The closed primitive atom classes. The scanner recognizes exactly these;
/// identifiers (class 3) are composed later, only where the structural or
/// math grammar requests one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AtomClass {
    /// Backslash plus ASCII letters, or backslash plus one ASCII nonletter.
    Control,
    /// One or more ASCII letters.
    Word,
    /// One or more ASCII digits.
    Numeral,
    /// One of `{`, `}`, `(`, `)`, `[`, `]`.
    Delimiter,
    /// One printable ASCII scalar not classified above.
    AsciiSymbol,
    /// One non-ASCII Unicode scalar.
    UnicodeSymbol,
    /// One or more U+0020 or LF scalars.
    Whitespace,
}

impl AtomClass {
    /// The coverage-schema token for this class.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Control => "control",
            Self::Word => "word",
            Self::Numeral => "numeral",
            Self::Delimiter => "delimiter",
            Self::AsciiSymbol => "ascii-symbol",
            Self::UnicodeSymbol => "unicode-symbol",
            Self::Whitespace => "whitespace",
        }
    }
}

/// One scanned atom with exact byte and line/column spans (§12.2). Lines and
/// columns are one-based; columns count Unicode scalar values after
/// normalization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Atom {
    /// The atom class.
    pub class: AtomClass,
    /// Start byte offset in the normalized source.
    pub byte_start: usize,
    /// End byte offset, exclusive.
    pub byte_end: usize,
    /// One-based start line.
    pub line_start: usize,
    /// One-based start column.
    pub column_start: usize,
    /// One-based end line.
    pub line_end: usize,
    /// One-based end column.
    pub column_end: usize,
    /// The atom text.
    pub text: String,
}

impl Atom {
    /// The diagnostic span for this atom in `path`.
    #[must_use]
    pub fn span(&self, path: &str) -> crate::diagnostic::Span {
        crate::diagnostic::Span {
            path: path.to_owned(),
            byte_start: self.byte_start,
            byte_end: self.byte_end,
            line_start: self.line_start,
            column_start: self.column_start,
            line_end: self.line_end,
            column_end: self.column_end,
        }
    }
}
