//! Source decoding and normalization (SPEC.md §12.1).

use unicode_normalization::{is_nfc, UnicodeNormalization};

use crate::diagnostic::{Diagnostic, Span};
use crate::{code, diagnostic::DiagnosticCode};

/// The result of normalizing one source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Normalized {
    /// The normalized text: LF line endings, NFC, one final LF.
    pub text: String,
}

fn at_byte(path: &str, text: &str, byte: usize) -> Span {
    let prefix = &text[..byte.min(text.len())];
    let line = prefix.matches('\n').count() + 1;
    let column = prefix
        .rsplit('\n')
        .next()
        .map_or(1, |tail| tail.chars().count() + 1);
    Span {
        path: path.to_owned(),
        byte_start: byte,
        byte_end: byte,
        line_start: line,
        column_start: column,
        line_end: line,
        column_end: column,
    }
}

fn reject(code: DiagnosticCode, path: &str, text: &str, byte: usize, message: &str) -> Diagnostic {
    Diagnostic::new(code, message).with_span(at_byte(path, text, byte))
}

/// The non-ASCII whitespace scalars §12.1 forbids, as an explicit list (the
/// scanner and normalizer have no dependency on host Unicode classes): the
/// line and paragraph separators, NEL, and every Unicode `White_Space`
/// scalar outside ASCII.
pub const NON_ASCII_WHITESPACE: [char; 20] = [
    '\u{0085}', '\u{00A0}', '\u{1680}', '\u{2000}', '\u{2001}', '\u{2002}', '\u{2003}', '\u{2004}',
    '\u{2005}', '\u{2006}', '\u{2007}', '\u{2008}', '\u{2009}', '\u{200A}', '\u{2028}', '\u{2029}',
    '\u{202F}', '\u{205F}', '\u{3000}', '\u{FEFF}',
];

/// Decode and normalize `.lex.tex` bytes (§12.1): valid UTF-8, CRLF and lone
/// CR to LF, NFC required, one final LF, and none of the forbidden scalars.
/// `for_fmt` additionally applies NFC and trims surplus final LFs instead of
/// rejecting them, because `fmt` rewrites such source canonically.
pub fn normalize(path: &str, bytes: &[u8], for_fmt: bool) -> Result<Normalized, Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();

    if bytes.starts_with(&[0xEF, 0xBB, 0xBF]) {
        diagnostics.push(
            Diagnostic::new(code!("LLL1001"), "a byte-order mark is forbidden")
                .with_span(Span::whole_file(path)),
        );
        return Err(diagnostics);
    }
    let raw = match std::str::from_utf8(bytes) {
        Ok(text) => text,
        Err(error) => {
            diagnostics.push(
                Diagnostic::new(
                    code!("LLL1001"),
                    format!("source is not valid UTF-8 at byte {}", error.valid_up_to()),
                )
                .with_span(Span::whole_file(path)),
            );
            return Err(diagnostics);
        }
    };

    // CRLF and lone CR to LF first (§12.1), so every later offset is over the
    // line-normalized text.
    let text: String = {
        let mut out = String::with_capacity(raw.len());
        let mut chars = raw.chars().peekable();
        while let Some(c) = chars.next() {
            if c == '\r' {
                if chars.peek() == Some(&'\n') {
                    chars.next();
                }
                out.push('\n');
            } else {
                out.push(c);
            }
        }
        out
    };

    let nfc_text;
    let text: &str = if is_nfc(&text) {
        &text
    } else if for_fmt {
        nfc_text = text.nfc().collect::<String>();
        &nfc_text
    } else {
        diagnostics.push(
            Diagnostic::new(code!("LLL1003"), "source is not Unicode NFC")
                .with_span(Span::whole_file(path))
                .with_help("run `lexlean fmt` to rewrite the file canonically"),
        );
        return Err(diagnostics);
    };

    for (byte, scalar) in text.char_indices() {
        match scalar {
            '\0' => diagnostics.push(reject(
                code!("LLL1001"),
                path,
                text,
                byte,
                "NUL is forbidden",
            )),
            '\t' => diagnostics.push(reject(
                code!("LLL1002"),
                path,
                text,
                byte,
                "tab is forbidden",
            )),
            '%' => diagnostics.push(
                reject(
                    code!("LLL1002"),
                    path,
                    text,
                    byte,
                    "a raw percent character is forbidden; TeX comments do not exist",
                )
                .with_help("a percent sign may appear only through a glossary-defined control sequence such as \\percent"),
            ),
            '\u{2028}' | '\u{2029}' => diagnostics.push(reject(
                code!("LLL1001"),
                path,
                text,
                byte,
                "Unicode line and paragraph separators are forbidden",
            )),
            '\u{FEFF}' if byte > 0 => diagnostics.push(reject(
                code!("LLL1001"),
                path,
                text,
                byte,
                "a byte-order mark inside the file is forbidden",
            )),
            c if NON_ASCII_WHITESPACE.contains(&c) => diagnostics.push(reject(
                code!("LLL1001"),
                path,
                text,
                byte,
                &format!("non-ASCII whitespace U+{:04X} is forbidden", u32::from(c)),
            )),
            // Other ASCII control scalars (besides tab, LF, and NUL, which
            // have their own messages) match no atom class.
            c if c.is_ascii_control() && c != '\n' && c != '\t' && c != '\0' => {
                diagnostics.push(reject(
                    code!("LLL1001"),
                    path,
                    text,
                    byte,
                    &format!("forbidden scalar U+{:04X}", u32::from(c)),
                ));
            }
            _ => {}
        }
    }

    for (index, line) in text.split('\n').enumerate() {
        if line.ends_with(' ') {
            let line_start: usize = text.split_inclusive('\n').take(index).map(str::len).sum();
            diagnostics.push(reject(
                code!("LLL1001"),
                path,
                text,
                line_start + line.len().saturating_sub(1),
                "trailing spaces are forbidden",
            ));
        }
    }

    if !text.ends_with('\n') {
        diagnostics.push(
            Diagnostic::new(code!("LLL1001"), "a source file must end in one LF")
                .with_span(Span::whole_file(path)),
        );
    }
    // Exactly one final LF (§12.1): surplus final LFs are noncanonical
    // source that formatting removes.
    let trimmed_text;
    let text: &str = if text.ends_with("\n\n") {
        if for_fmt {
            trimmed_text = format!("{}\n", text.trim_end_matches('\n'));
            &trimmed_text
        } else {
            let surplus_start = text.trim_end_matches('\n').len() + 1;
            diagnostics.push(
                reject(
                    code!("LLL1003"),
                    path,
                    text,
                    surplus_start,
                    "a source file must end in exactly one LF",
                )
                .with_help("remove the surplus final line breaks, or run `lexlean fmt`"),
            );
            text
        }
    } else {
        text
    };

    if diagnostics.is_empty() {
        Ok(Normalized {
            text: text.to_owned(),
        })
    } else {
        Err(diagnostics)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn codes(result: Result<Normalized, Vec<Diagnostic>>) -> Vec<&'static str> {
        result
            .err()
            .unwrap_or_default()
            .iter()
            .map(|d| d.code.as_str())
            .collect()
    }

    #[test]
    fn line_endings_and_final_lf() {
        let ok = normalize("m", b"a\r\nb\rc\n", false).expect("normalizes");
        assert_eq!(ok.text, "a\nb\nc\n");
        assert_eq!(codes(normalize("m", b"a", false)), vec!["LLL1001"]);
        assert_eq!(codes(normalize("m", b"a\n\n", false)), vec!["LLL1003"]);
        assert_eq!(codes(normalize("m", b"a\n\n\n", false)), vec!["LLL1003"]);
        assert_eq!(
            normalize("m", b"a\n\n\n", true).expect("fmt trims").text,
            "a\n"
        );
        assert_eq!(codes(normalize("m", b"\n\n", false)), vec!["LLL1003"]);
        assert!(normalize("m", b"\n", false).is_ok());
    }

    #[test]
    fn forbidden_scalars() {
        assert_eq!(
            codes(normalize("m", b"\xEF\xBB\xBFa\n", false)),
            vec!["LLL1001"]
        );
        assert_eq!(codes(normalize("m", b"a\xFF\n", false)), vec!["LLL1001"]);
        assert_eq!(codes(normalize("m", b"a\0\n", false)), vec!["LLL1001"]);
        assert_eq!(codes(normalize("m", b"a\tb\n", false)), vec!["LLL1002"]);
        assert_eq!(codes(normalize("m", b"a % b\n", false)), vec!["LLL1002"]);
        assert_eq!(codes(normalize("m", b"a \n", false)), vec!["LLL1001"]);
        assert_eq!(
            codes(normalize("m", "a\u{2028}b\n".as_bytes(), false)),
            vec!["LLL1001"]
        );
        assert_eq!(
            codes(normalize("m", "a\u{00A0}b\n".as_bytes(), false)),
            vec!["LLL1001"]
        );
        assert_eq!(
            codes(normalize("m", "a\u{3000}b\n".as_bytes(), false)),
            vec!["LLL1001"]
        );
        assert_eq!(
            codes(normalize("m", "a\u{FEFF}b\n".as_bytes(), false)),
            vec!["LLL1001"]
        );
        assert_eq!(codes(normalize("m", b"a\x0Bb\n", false)), vec!["LLL1001"]);
        assert_eq!(
            codes(normalize("m", "n\u{0303}\n".as_bytes(), false)),
            vec!["LLL1003"]
        );
        assert_eq!(
            normalize("m", "n\u{0303}\n".as_bytes(), true)
                .expect("fmt composes")
                .text,
            "\u{00F1}\n"
        );
    }

    #[test]
    fn spans_point_at_the_offending_scalar() {
        let error = normalize("m", b"ab\tc\n", false).expect_err("tab");
        let span = error[0].primary.as_ref().expect("span");
        assert_eq!((span.line_start, span.column_start), (1, 3));
        let error = normalize("m", "x\n\u{00A0}\n".as_bytes(), false).expect_err("nbsp");
        let span = error[0].primary.as_ref().expect("span");
        assert_eq!((span.line_start, span.column_start), (2, 1));
    }
}
