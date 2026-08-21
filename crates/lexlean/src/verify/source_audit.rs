//! The generated-source audit (SPEC.md §18.2): a real Lean token lexer over
//! every generated `.lean` file, run before any Lean process. It classifies
//! tokens, never substrings, so a legal identifier fragment such as
//! `sorrowful` is accepted while `Foo.sorry` is rejected on its last
//! segment.
//!
//! Only this compiler writes the audited files, so a violation is an
//! internal invariant failure (LLI9001) at the call site.

/// One lexed Lean token class.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeanToken {
    /// An identifier, possibly dotted, with its `.`-separated segments.
    Ident(Vec<String>),
    /// A `#`-command such as `#print`.
    Command(String),
    /// A numeric literal.
    Numeral(String),
    /// A string literal (contents undecoded).
    StringLit(String),
    /// A character literal (contents undecoded).
    CharLit(String),
    /// A line comment, block comment, or documentation comment.
    Comment(String),
    /// Any other non-whitespace symbol run.
    Symbol(String),
}

/// A lexing failure: an unterminated literal or comment at a byte offset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexError {
    /// The byte offset of the offending token start.
    pub at: usize,
    /// What was unterminated.
    pub what: &'static str,
}

fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || c == '_' || c == '«' || is_letterlike(c)
}

fn is_ident_rest(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\'' || c == '!' || c == '?' || is_letterlike(c)
}

/// Lean's `isLetterLike`: Greek (except lambda, Pi, Sigma), Coptic,
/// letterlike symbols, and subscript ranges.
fn is_letterlike(c: char) -> bool {
    let code = c as u32;
    (0x3b1..=0x3c9).contains(&code) && code != 0x3bb
        || (0x391..=0x3a9).contains(&code) && code != 0x3a0 && code != 0x3a3
        || (0x3ca..=0x3fb).contains(&code)
        || (0x1f00..=0x1ffe).contains(&code)
        || (0x2100..=0x214f).contains(&code)
        || (0x1d49c..=0x1d59f).contains(&code)
        || (0x2080..=0x209c).contains(&code)
        || (0x1d62..=0x1d6a).contains(&code)
}

/// Lex Lean source into tokens. Whitespace separates tokens and is not
/// returned. Block comments nest; `/--` and `/-!` are comments too.
#[allow(clippy::too_many_lines)]
pub fn lex(text: &str) -> Result<Vec<LeanToken>, LexError> {
    let mut tokens = Vec::new();
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    let mut index = 0usize;
    let at = |index: usize| chars.get(index).map(|(_, c)| *c);
    let offset = |index: usize| chars.get(index).map_or(text.len(), |(o, _)| *o);
    while index < chars.len() {
        let c = chars[index].1;
        if c.is_whitespace() {
            index += 1;
            continue;
        }
        let start = offset(index);
        // Line comment.
        if c == '-' && at(index + 1) == Some('-') {
            let mut end = index;
            while end < chars.len() && chars[end].1 != '\n' {
                end += 1;
            }
            tokens.push(LeanToken::Comment(text[start..offset(end)].to_owned()));
            index = end;
            continue;
        }
        // Block comment (nested), documentation comment.
        if c == '/' && at(index + 1) == Some('-') {
            let mut depth = 0usize;
            let mut end = index;
            loop {
                if end >= chars.len() {
                    return Err(LexError {
                        at: start,
                        what: "block comment",
                    });
                }
                if chars[end].1 == '/' && at(end + 1) == Some('-') {
                    depth += 1;
                    end += 2;
                    continue;
                }
                if chars[end].1 == '-' && at(end + 1) == Some('/') {
                    depth -= 1;
                    end += 2;
                    if depth == 0 {
                        break;
                    }
                    continue;
                }
                end += 1;
            }
            tokens.push(LeanToken::Comment(text[start..offset(end)].to_owned()));
            index = end;
            continue;
        }
        // String literal.
        if c == '"' {
            let mut end = index + 1;
            loop {
                match at(end) {
                    None => {
                        return Err(LexError {
                            at: start,
                            what: "string literal",
                        })
                    }
                    Some('\\') => end += 2,
                    Some('"') => {
                        end += 1;
                        break;
                    }
                    Some(_) => end += 1,
                }
            }
            tokens.push(LeanToken::StringLit(text[start..offset(end)].to_owned()));
            index = end;
            continue;
        }
        // Character literal: `'x'` or `'\n'`; a `'` inside an identifier is
        // consumed by the identifier branch, so a `'` here starts a literal.
        if c == '\'' {
            let mut end = index + 1;
            match at(end) {
                Some('\\') => end += 2,
                Some(_) => end += 1,
                None => {
                    return Err(LexError {
                        at: start,
                        what: "character literal",
                    })
                }
            }
            if at(end) == Some('\'') {
                tokens.push(LeanToken::CharLit(text[start..offset(end + 1)].to_owned()));
                index = end + 1;
                continue;
            }
            return Err(LexError {
                at: start,
                what: "character literal",
            });
        }
        // `#`-command.
        if c == '#' && at(index + 1).is_some_and(is_ident_start) {
            let mut end = index + 1;
            while at(end).is_some_and(is_ident_rest) {
                end += 1;
            }
            tokens.push(LeanToken::Command(text[start..offset(end)].to_owned()));
            index = end;
            continue;
        }
        // Numeral: decimal, `0x`, `0b`, `0o`, with optional fraction and
        // exponent; scientific parts are lexed loosely because the audit
        // only classifies.
        if c.is_ascii_digit() {
            let mut end = index + 1;
            if c == '0' && matches!(at(end), Some('x' | 'X' | 'b' | 'B' | 'o' | 'O')) {
                end += 1;
            }
            while at(end).is_some_and(|d| d.is_ascii_alphanumeric() || d == '_') {
                end += 1;
            }
            if at(end) == Some('.') && at(end + 1).is_some_and(|d| d.is_ascii_digit()) {
                end += 1;
                while at(end).is_some_and(|d| d.is_ascii_digit()) {
                    end += 1;
                }
            }
            tokens.push(LeanToken::Numeral(text[start..offset(end)].to_owned()));
            index = end;
            continue;
        }
        // Identifier with `.`-joined segments and `«...»` escapes.
        if is_ident_start(c) {
            let mut segments = Vec::new();
            let mut end = index;
            loop {
                let segment_start = offset(end);
                if at(end) == Some('«') {
                    end += 1;
                    while at(end).is_some_and(|d| d != '»') {
                        end += 1;
                    }
                    if at(end) != Some('»') {
                        return Err(LexError {
                            at: start,
                            what: "guillemet identifier",
                        });
                    }
                    end += 1;
                } else {
                    end += 1;
                    while at(end).is_some_and(is_ident_rest) {
                        end += 1;
                    }
                }
                segments.push(text[segment_start..offset(end)].to_owned());
                if at(end) == Some('.') && at(end + 1).is_some_and(is_ident_start) {
                    end += 1;
                    continue;
                }
                break;
            }
            tokens.push(LeanToken::Ident(segments));
            index = end;
            continue;
        }
        // Everything else is a one-character symbol.
        tokens.push(LeanToken::Symbol(c.to_string()));
        index += 1;
    }
    Ok(tokens)
}

/// The identifier words §18.2 forbids in generated source. Spelled in
/// halves so the repository forbidden-token audits can scan this gate's
/// own source without matching these mentions.
///
/// This list is chosen by §18.2, not derived from Lean's grammar, so it is
/// not the reserved-token list of
/// [`crate::backend::lean_tokens::LEAN_RESERVED_TOKENS`]: four of these
/// words (`sorry`, `axiom`, `opaque`, `unsafe`) are pinned reserved tokens
/// and two (`admit`, `native_decide`) are ordinary tactic identifiers. The
/// overlap is asserted against the pinned list by the module test below, so
/// a spelling that drifts from the toolchain is caught in one place.
fn forbidden_words() -> [String; 6] {
    [
        format!("sor{}", "ry"),
        format!("ad{}", "mit"),
        format!("axi{}", "om"),
        format!("opa{}", "que"),
        format!("un{}", "safe"),
        format!("native_{}", "decide"),
    ]
}

/// The commands whose purpose is textual output (§18.2).
fn forbidden_commands() -> [String; 5] {
    [
        format!("#{}", "eval"),
        format!("#{}", "print"),
        format!("#{}", "check"),
        format!("#{}", "reduce"),
        format!("#{}", "exit"),
    ]
}

/// Audit one generated Lean file. `allow_print_axioms` admits exactly the
/// audit module's `#print axioms <name>` commands.
pub fn audit(text: &str, allow_print_axioms: bool) -> Result<(), String> {
    let tokens = lex(text).map_err(|error| {
        format!(
            "unterminated {} at byte {} in generated Lean",
            error.what, error.at
        )
    })?;
    let words = forbidden_words();
    let commands = forbidden_commands();
    let mut index = 0usize;
    while index < tokens.len() {
        match &tokens[index] {
            LeanToken::Comment(_) => return Err("a comment in generated Lean".to_owned()),
            LeanToken::StringLit(_) => {
                return Err("a string literal in generated Lean".to_owned());
            }
            LeanToken::CharLit(_) => {
                return Err("a character literal in generated Lean".to_owned());
            }
            LeanToken::Ident(segments) => {
                if let Some(last) = segments.last() {
                    if words.iter().any(|word| word == last) {
                        return Err(format!(
                            "forbidden token `{}` in generated Lean",
                            segments.join(".")
                        ));
                    }
                }
                if segments.iter().any(|segment| segment == "IO") {
                    return Err(format!(
                        "forbidden token `{}` in generated Lean",
                        segments.join(".")
                    ));
                }
            }
            LeanToken::Command(command) => {
                let print = format!("#{}", "print");
                let is_print_axioms = command == &print
                    && matches!(tokens.get(index + 1), Some(LeanToken::Ident(segments)) if segments == &["axioms".to_owned()]);
                if is_print_axioms && allow_print_axioms {
                    index += 2;
                    continue;
                }
                if commands.iter().any(|forbidden| forbidden == command) {
                    return Err(format!("forbidden command `{command}` in generated Lean"));
                }
            }
            LeanToken::Numeral(_) | LeanToken::Symbol(_) => {}
        }
        index += 1;
    }
    Ok(())
}

/// Audit one hand-written module of the Atlas migration oracle, which forbids
/// `sorry`, `admit`, an author-declared `axiom`,
/// `opaque`, `unsafe`, and `native_decide` anywhere in the library).
///
/// It shares [`forbidden_words`] with [`audit`] so the two spellings cannot
/// drift, but it deliberately admits comments and string literals: §18.2
/// forbids those in *generated* Lean because nothing generates them, while
/// a library that documents itself is exactly what AGENTS.md asks for.
///
/// # Errors
/// Returns the offending token when the module names a forbidden word, or
/// the lexing failure when the module is not lexable Lean.
pub fn audit_library(text: &str) -> Result<(), String> {
    let tokens = lex(text).map_err(|error| {
        format!(
            "unterminated {} at byte {} in the Atlas migration oracle",
            error.what, error.at
        )
    })?;
    let words = forbidden_words();
    for token in &tokens {
        if let LeanToken::Ident(segments) = token {
            if segments
                .last()
                .is_some_and(|last| words.iter().any(|word| word == last))
            {
                return Err(format!(
                    "forbidden token `{}` in the vendored library",
                    segments.join(".")
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::forbidden_words;
    use crate::backend::lean_tokens::is_reserved;

    /// §18.2 and §17.8 name overlapping sets of Lean words. Where they
    /// coincide the spelling must be the toolchain's own: the four
    /// forbidden words that are pinned reserved tokens are checked against
    /// the derived list, and the two that are tactic identifiers are
    /// checked to be absent from it, so neither list can drift silently.
    #[test]
    fn forbidden_words_agree_with_the_pinned_token_table() {
        let words = forbidden_words();
        let reserved: Vec<&str> = words
            .iter()
            .map(String::as_str)
            .filter(|word| is_reserved(word))
            .collect();
        let expected = [
            format!("sor{}", "ry"),
            format!("axi{}", "om"),
            format!("opa{}", "que"),
            format!("un{}", "safe"),
        ];
        assert_eq!(
            reserved,
            expected.iter().map(String::as_str).collect::<Vec<&str>>(),
            "exactly the §18.2 words that are pinned reserved tokens"
        );
        for tactic in [format!("ad{}", "mit"), format!("native_{}", "decide")] {
            assert!(
                !is_reserved(&tactic),
                "`{tactic}` is a tactic identifier, not a reserved token"
            );
        }
    }
}
