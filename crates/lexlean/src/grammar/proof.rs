//! The simple proof sentence grammar (SPEC.md §16.2): the exact registered
//! sentences and nothing else. Arbitrary imperative sentences and
//! unregistered synonyms are rejected (§16.12).

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::grammar::chart::TextToken;
use crate::grammar::proposition::{Keyword, TextParser};
use crate::source::atom::AtomClass;

/// One parsed simple proof sentence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SentenceAstKind {
    /// `Assume \(x\).` or `Assume \(x\), \(y\).`
    Assume {
        /// The fresh-local islands, in order.
        islands: Vec<TextToken>,
    },
    /// `Apply TERM.`
    Apply {
        /// The proof-term island.
        term: TextToken,
    },
    /// `Close the goal with TERM.`
    CloseWith {
        /// The proof-term island.
        term: TextToken,
    },
    /// `Close the goal by reflexivity.`
    CloseByReflexivity,
    /// `Use TERM as the witness.`
    Witness {
        /// The witness island.
        term: TextToken,
    },
    /// `Select the left alternative.`
    SelectLeft,
    /// `Select the right alternative.`
    SelectRight,
}

/// A parsed sentence with its coverage keywords.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofSentence {
    /// The sentence kind.
    pub kind: SentenceAstKind,
    /// Every keyword occurrence, for coverage.
    pub keywords: Vec<Keyword>,
}

/// The proof keyword vocabulary: word to covering core entry.
#[must_use]
pub fn proof_keyword_entry(word: &str) -> Option<&'static str> {
    Some(match word {
        "Assume" => "assume",
        "Apply" => "apply-verb",
        "Close" => "close",
        "Select" => "select",
        "Use" => "use",
        "alternative" => "alternative",
        "as" => "as",
        "by" => "by",
        "goal" => "goal",
        "left" => "left",
        "reflexivity" => "reflexivity",
        "right" => "right",
        "the" => "the",
        "with" => "with",
        "witness" => "witness",
        _ => return None,
    })
}

struct Matcher<'a, 'b> {
    parser: &'b TextParser<'a>,
    pos: usize,
    keywords: Vec<Keyword>,
}

impl Matcher<'_, '_> {
    fn word(&mut self, expected: &str) -> bool {
        let Some(TextToken::Atom(index)) = self.parser.tokens.get(self.pos) else {
            return false;
        };
        let atom = &self.parser.atoms[*index];
        if atom.class == AtomClass::Word && atom.text == expected {
            if let Some(entry) = proof_keyword_entry(expected) {
                self.keywords.push(Keyword {
                    atom: *index,
                    entry,
                });
            }
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn island(&mut self) -> Option<TextToken> {
        match self.parser.tokens.get(self.pos) {
            Some(token @ TextToken::Island { .. }) => {
                self.pos += 1;
                Some(token.clone())
            }
            _ => None,
        }
    }

    fn comma(&mut self) -> bool {
        let Some(TextToken::Atom(index)) = self.parser.tokens.get(self.pos) else {
            return false;
        };
        let atom = &self.parser.atoms[*index];
        if atom.class == AtomClass::AsciiSymbol && atom.text == "," {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn done(&self) -> bool {
        self.pos == self.parser.tokens.len()
    }
}

/// Parse one simple proof sentence's tokens (the terminating period is
/// outside the range). Anything not in the registered set is a forbidden
/// proof form (§16.12).
pub fn parse_proof_sentence(parser: &TextParser<'_>) -> Result<ProofSentence, Diagnostic> {
    let fail = || {
        let span = parser.tokens.first().map_or_else(
            || crate::diagnostic::Span::whole_file(parser.path),
            |token| parser.atoms[token.first_atom()].span(parser.path),
        );
        Diagnostic::new(
            code!("LLF5005"),
            "not a registered proof sentence; the exact simple sentences are fixed",
        )
        .with_span(span)
    };

    let mut matcher = Matcher {
        parser,
        pos: 0,
        keywords: Vec::new(),
    };
    if matcher.word("Assume") {
        let mut islands = Vec::new();
        let Some(first) = matcher.island() else {
            return Err(fail());
        };
        islands.push(first);
        while matcher.comma() {
            let Some(next) = matcher.island() else {
                return Err(fail());
            };
            islands.push(next);
        }
        if !matcher.done() {
            return Err(fail());
        }
        return Ok(ProofSentence {
            kind: SentenceAstKind::Assume { islands },
            keywords: matcher.keywords,
        });
    }
    if matcher.word("Apply") {
        let Some(term) = matcher.island() else {
            return Err(fail());
        };
        if !matcher.done() {
            return Err(fail());
        }
        return Ok(ProofSentence {
            kind: SentenceAstKind::Apply { term },
            keywords: matcher.keywords,
        });
    }
    if matcher.word("Close") {
        if !(matcher.word("the") && matcher.word("goal")) {
            return Err(fail());
        }
        if matcher.word("with") {
            let Some(term) = matcher.island() else {
                return Err(fail());
            };
            if !matcher.done() {
                return Err(fail());
            }
            return Ok(ProofSentence {
                kind: SentenceAstKind::CloseWith { term },
                keywords: matcher.keywords,
            });
        }
        if matcher.word("by") && matcher.word("reflexivity") && matcher.done() {
            return Ok(ProofSentence {
                kind: SentenceAstKind::CloseByReflexivity,
                keywords: matcher.keywords,
            });
        }
        return Err(fail());
    }
    if matcher.word("Use") {
        let Some(term) = matcher.island() else {
            return Err(fail());
        };
        if matcher.word("as") && matcher.word("the") && matcher.word("witness") && matcher.done() {
            return Ok(ProofSentence {
                kind: SentenceAstKind::Witness { term },
                keywords: matcher.keywords,
            });
        }
        return Err(fail());
    }
    if matcher.word("Select") {
        if !matcher.word("the") {
            return Err(fail());
        }
        let left = matcher.word("left");
        let right = !left && matcher.word("right");
        if (left || right) && matcher.word("alternative") && matcher.done() {
            return Ok(ProofSentence {
                kind: if left {
                    SentenceAstKind::SelectLeft
                } else {
                    SentenceAstKind::SelectRight
                },
                keywords: matcher.keywords,
            });
        }
        return Err(fail());
    }
    Err(fail())
}
