//! Source decoding and normalization (SPEC.md §12.1).

use unicode_normalization::{is_nfc, UnicodeNormalization};

use crate::diagnostic::{Diagnostic, Span};
use crate::{code, diagnostic::DiagnosticCode};

/// The result of normalizing one source file.
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

/// Decode and normalize `.lex.tex` bytes (§12.1): valid UTF-8, CRLF and lone
/// CR to LF, NFC required, one final LF, and none of the forbidden scalars.
/// `for_fmt` additionally applies NFC instead of rejecting it, because `fmt`
/// rewrites non-NFC source canonically.
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
            '\u{2028}' | '\u{2029}' | '\u{0085}' => diagnostics.push(reject(
                code!("LLL1001"),
                path,
                text,
                byte,
                "Unicode line and paragraph separators are forbidden",
            )),
            c if c != ' ' && c != '\n' && c.is_whitespace() => diagnostics.push(reject(
                code!("LLL1001"),
                path,
                text,
                byte,
                "non-ASCII whitespace is forbidden",
            )),
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

    if !text.ends_with('\n') || text.ends_with("\n\n") && text.trim_end_matches('\n').is_empty() {
        diagnostics.push(
            Diagnostic::new(code!("LLL1001"), "a source file must end in one LF")
                .with_span(Span::whole_file(path)),
        );
    }

    if diagnostics.is_empty() {
        Ok(Normalized {
            text: text.to_owned(),
        })
    } else {
        Err(diagnostics)
    }
}
