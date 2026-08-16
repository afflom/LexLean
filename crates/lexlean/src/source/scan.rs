//! The primitive scanner (SPEC.md §12.2).
//!
//! Recognizes exactly the eight atom classes with byte and line/column
//! spans. It assigns no mathematical meaning, has no dependency on host
//! Unicode character classes, and is the only bootstrapping layer (§12.3).

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::source::atom::{Atom, AtomClass};

/// Position bookkeeping for one-based lines and scalar-counting columns.
struct Cursor<'a> {
    text: &'a str,
    byte: usize,
    line: usize,
    column: usize,
}

impl<'a> Cursor<'a> {
    fn peek(&self) -> Option<char> {
        self.text[self.byte..].chars().next()
    }

    fn bump(&mut self) -> Option<char> {
        let scalar = self.peek()?;
        self.byte += scalar.len_utf8();
        if scalar == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(scalar)
    }
}

/// Scan normalized source into primitive atoms. `max_primitive_atoms` is the
/// explicit resource limit (§10.2); exceeding it is `LLS8002`.
pub fn scan(path: &str, text: &str, max_primitive_atoms: u64) -> Result<Vec<Atom>, Diagnostic> {
    let mut cursor = Cursor {
        text,
        byte: 0,
        line: 1,
        column: 1,
    };
    let mut atoms: Vec<Atom> = Vec::new();

    while let Some(scalar) = cursor.peek() {
        let byte_start = cursor.byte;
        let line_start = cursor.line;
        let column_start = cursor.column;

        let class = match scalar {
            ' ' | '\n' => {
                while matches!(cursor.peek(), Some(' ' | '\n')) {
                    cursor.bump();
                }
                AtomClass::Whitespace
            }
            '\\' => {
                cursor.bump();
                match cursor.peek() {
                    Some(next) if next.is_ascii_alphabetic() => {
                        while matches!(cursor.peek(), Some(c) if c.is_ascii_alphabetic()) {
                            cursor.bump();
                        }
                    }
                    Some(next) if next.is_ascii() => {
                        cursor.bump();
                    }
                    _ => {
                        // A backslash followed by a non-ASCII scalar or end
                        // of file matches no atom class (§12.2 class 1 needs
                        // one ASCII nonletter).
                        return Err(Diagnostic::new(
                            code!("LLL1004"),
                            "a control sequence needs ASCII letters or one ASCII nonletter after the backslash",
                        )
                        .with_span(crate::diagnostic::Span {
                            path: path.to_owned(),
                            byte_start,
                            byte_end: cursor.byte,
                            line_start,
                            column_start,
                            line_end: cursor.line,
                            column_end: cursor.column,
                        }));
                    }
                }
                AtomClass::Control
            }
            c if c.is_ascii_alphabetic() => {
                while matches!(cursor.peek(), Some(x) if x.is_ascii_alphabetic()) {
                    cursor.bump();
                }
                AtomClass::Word
            }
            c if c.is_ascii_digit() => {
                while matches!(cursor.peek(), Some(x) if x.is_ascii_digit()) {
                    cursor.bump();
                }
                AtomClass::Numeral
            }
            '{' | '}' | '(' | ')' | '[' | ']' => {
                cursor.bump();
                AtomClass::Delimiter
            }
            c if c.is_ascii() && (' '..='~').contains(&c) => {
                cursor.bump();
                AtomClass::AsciiSymbol
            }
            c if !c.is_ascii() => {
                cursor.bump();
                AtomClass::UnicodeSymbol
            }
            _ => {
                // Remaining ASCII scalars are control characters, all of
                // which normalization already rejected (§12.1); reaching one
                // here is an unprintable byte that no class covers.
                return Err(Diagnostic::new(
                    code!("LLL1001"),
                    format!("forbidden scalar U+{:04X}", scalar as u32),
                )
                .with_span(crate::diagnostic::Span {
                    path: path.to_owned(),
                    byte_start,
                    byte_end: byte_start + scalar.len_utf8(),
                    line_start,
                    column_start,
                    line_end: line_start,
                    column_end: column_start + 1,
                }));
            }
        };

        atoms.push(Atom {
            class,
            byte_start,
            byte_end: cursor.byte,
            line_start,
            column_start,
            line_end: cursor.line,
            column_end: cursor.column,
            text: text[byte_start..cursor.byte].to_owned(),
        });
        if atoms.len() as u64 > max_primitive_atoms {
            return Err(Diagnostic::new(
                code!("LLS8002"),
                format!(
                    "max_primitive_atoms exceeded: configured {max_primitive_atoms}, scanning {path}"
                ),
            ));
        }
    }
    Ok(atoms)
}

/// Post-scan atom rejections that need no glossary (§12.4, §15.5): a
/// control atom in the always-forbidden set (from
/// `language/bootstrap.toml`, the single source of truth) is `LLL1002` with
/// its span, before any lexical resolution; a standalone numeral with a
/// redundant leading zero is noncanonical decimal source (`LLL1003`, with a
/// fix-it), because §13.8 decimals and the numeral constructor share one
/// canonical spelling. A numeral byte-adjacent after identifier material
/// (`x01`, `add-01`) is part of a composed identifier and is not a numeral.
pub fn reject_forbidden_atoms(
    path: &str,
    atoms: &[Atom],
    forbidden_controls: &[String],
) -> Result<(), Diagnostic> {
    for (index, atom) in atoms.iter().enumerate() {
        match atom.class {
            AtomClass::Control => {
                if forbidden_controls
                    .iter()
                    .any(|forbidden| forbidden == &atom.text)
                {
                    return Err(Diagnostic::new(
                        code!("LLL1002"),
                        format!(
                            "`{}` is an always-forbidden TeX control (§12.4); LexLean does not expand TeX",
                            atom.text
                        ),
                    )
                    .with_span(atom.span(path)));
                }
            }
            AtomClass::Numeral if atom.text.len() > 1 && atom.text.starts_with('0') => {
                let continues_identifier = index
                    .checked_sub(1)
                    .and_then(|previous| atoms.get(previous))
                    .is_some_and(|previous| {
                        previous.byte_end == atom.byte_start
                            && match previous.class {
                                AtomClass::Word => true,
                                AtomClass::AsciiSymbol => {
                                    matches!(previous.text.as_str(), "_" | "'" | "-")
                                }
                                _ => false,
                            }
                    });
                if !continues_identifier {
                    let canonical = atom.text.trim_start_matches('0');
                    let canonical = if canonical.is_empty() { "0" } else { canonical };
                    return Err(Diagnostic::new(
                            code!("LLL1003"),
                            format!(
                                "numeral `{}` has a redundant leading zero; the canonical decimal is `{canonical}`",
                                atom.text
                            ),
                        )
                        .with_span(atom.span(path))
                        .with_help(format!("replace `{}` with `{canonical}`", atom.text)));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Compose a metadata/math identifier (§12.2 class 3) starting at atom
/// `index`: an ASCII letter run, then contiguous letters, digits, `_`, or
/// `'` atoms with no whitespace between them. Returns the identifier text
/// and the exclusive end atom index.
#[must_use]
pub fn compose_identifier(atoms: &[Atom], index: usize) -> Option<(String, usize)> {
    let first = atoms.get(index)?;
    if first.class != AtomClass::Word {
        return None;
    }
    let mut text = first.text.clone();
    let mut end = index + 1;
    let mut last_byte_end = first.byte_end;
    while let Some(atom) = atoms.get(end) {
        if atom.byte_start != last_byte_end {
            break;
        }
        let continues = match atom.class {
            AtomClass::Word | AtomClass::Numeral => true,
            AtomClass::AsciiSymbol => atom.text == "_" || atom.text == "'",
            _ => false,
        };
        if !continues {
            break;
        }
        text.push_str(&atom.text);
        last_byte_end = atom.byte_end;
        end += 1;
    }
    Some((text, end))
}

/// The span covering atoms `[start, end)` in `path`.
#[must_use]
pub fn atoms_span(path: &str, atoms: &[Atom], start: usize, end: usize) -> crate::diagnostic::Span {
    let first = &atoms[start];
    let last = &atoms[end.saturating_sub(1).max(start)];
    crate::diagnostic::Span {
        path: path.to_owned(),
        byte_start: first.byte_start,
        byte_end: last.byte_end,
        line_start: first.line_start,
        column_start: first.column_start,
        line_end: last.line_end,
        column_end: last.column_end,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn classes(text: &str) -> Vec<(AtomClass, String)> {
        scan("m", text, 1_000)
            .expect("scans")
            .into_iter()
            .map(|atom| (atom.class, atom.text))
            .collect()
    }

    #[test]
    fn the_eight_atom_classes() {
        assert_eq!(
            classes("\\begin{x} ab 12 + \u{2115}\n"),
            vec![
                (AtomClass::Control, "\\begin".to_owned()),
                (AtomClass::Delimiter, "{".to_owned()),
                (AtomClass::Word, "x".to_owned()),
                (AtomClass::Delimiter, "}".to_owned()),
                (AtomClass::Whitespace, " ".to_owned()),
                (AtomClass::Word, "ab".to_owned()),
                (AtomClass::Whitespace, " ".to_owned()),
                (AtomClass::Numeral, "12".to_owned()),
                (AtomClass::Whitespace, " ".to_owned()),
                (AtomClass::AsciiSymbol, "+".to_owned()),
                (AtomClass::Whitespace, " ".to_owned()),
                (AtomClass::UnicodeSymbol, "\u{2115}".to_owned()),
                (AtomClass::Whitespace, "\n".to_owned()),
            ]
        );
    }

    #[test]
    fn controls_take_letters_or_one_nonletter() {
        assert_eq!(
            classes("\\(x\\)"),
            vec![
                (AtomClass::Control, "\\(".to_owned()),
                (AtomClass::Word, "x".to_owned()),
                (AtomClass::Control, "\\)".to_owned()),
            ]
        );
        assert_eq!(
            classes("\\\\\\ \\1"),
            vec![
                (AtomClass::Control, "\\\\".to_owned()),
                (AtomClass::Control, "\\ ".to_owned()),
                (AtomClass::Control, "\\1".to_owned()),
            ]
        );
        assert_eq!(classes("\\ab1")[0], (AtomClass::Control, "\\ab".to_owned()));
        // A backslash before a non-ASCII scalar or at end of file matches no
        // class.
        assert_eq!(
            scan("m", "\\\u{2115}", 10)
                .expect_err("no class")
                .code
                .as_str(),
            "LLL1004"
        );
        assert_eq!(
            scan("m", "\\", 10).expect_err("no class").code.as_str(),
            "LLL1004"
        );
    }

    #[test]
    fn spans_are_exact_and_columns_count_scalars() {
        let atoms = scan("m", "\u{2115}\n+", 10).expect("scans");
        assert_eq!((atoms[0].byte_start, atoms[0].byte_end), (0, 3));
        assert_eq!((atoms[0].line_start, atoms[0].column_start), (1, 1));
        assert_eq!((atoms[0].line_end, atoms[0].column_end), (1, 2));
        assert_eq!((atoms[2].line_start, atoms[2].column_start), (2, 1));
        assert_eq!((atoms[2].byte_start, atoms[2].byte_end), (4, 5));
    }

    #[test]
    fn identifiers_compose_only_byte_adjacently() {
        let atoms = scan("m", "x1_2' y", 10).expect("scans");
        assert_eq!(compose_identifier(&atoms, 0), Some(("x1_2'".to_owned(), 5)));
        assert_eq!(compose_identifier(&atoms, 6), Some(("y".to_owned(), 7)));
        assert_eq!(compose_identifier(&atoms, 1), None);
        let spaced = scan("m", "x 1", 10).expect("scans");
        assert_eq!(compose_identifier(&spaced, 0), Some(("x".to_owned(), 1)));
    }

    #[test]
    fn atom_limit_is_a_limit_failure() {
        assert_eq!(
            scan("m", "a b c", 2).expect_err("limited").code.as_str(),
            "LLS8002"
        );
        assert!(scan("m", "", 0).expect("empty").is_empty());
    }

    #[test]
    fn forbidden_controls_and_leading_zeros() {
        let forbidden = vec!["\\def".to_owned(), "\\input".to_owned()];
        let atoms = scan("m", "a \\def b", 10).expect("scans");
        let error = reject_forbidden_atoms("m", &atoms, &forbidden).expect_err("forbidden");
        assert_eq!(error.code.as_str(), "LLL1002");
        assert_eq!(
            error.primary.as_ref().map(|s| (s.byte_start, s.byte_end)),
            Some((2, 6))
        );
        let atoms = scan("m", "a \\define b", 10).expect("scans");
        assert!(reject_forbidden_atoms("m", &atoms, &forbidden).is_ok());

        let atoms = scan("m", "n + 007", 10).expect("scans");
        let error = reject_forbidden_atoms("m", &atoms, &[]).expect_err("leading zero");
        assert_eq!(error.code.as_str(), "LLL1003");
        assert!(error.message.contains("`7`"));
        for ok in ["n + 0", "n + 70", "x01", "add-01", "x_01", "x'01", "f(0)"] {
            let atoms = scan("m", ok, 10).expect("scans");
            assert!(reject_forbidden_atoms("m", &atoms, &[]).is_ok(), "{ok}");
        }
        for bad in ["(01)", "00", "1.05"] {
            let atoms = scan("m", bad, 10).expect("scans");
            assert!(reject_forbidden_atoms("m", &atoms, &[]).is_err(), "{bad}");
        }
    }
}
