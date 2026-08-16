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
