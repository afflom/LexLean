//! Shared parsing machinery: explicit budgets and the text-token view the
//! controlled grammars consume (SPEC.md §14.1, §25.5).

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::source::atom::{Atom, AtomClass};

/// Checked parse budgets (§25.5). Exceeding a limit is `LLS8002`, never an
/// allocation panic or a stack overflow.
///
/// Limit mapping (§10.2): `max_scope_depth` bounds every form of
/// grammatical nesting --- section nesting, mathematical grouping and call
/// nesting, proposition connective nesting, nested proof environments ---
/// and, through the elaborator, the nesting depth of every linked IR term,
/// so that every recursive IR walker runs on a term of bounded depth.
/// `max_ir_nodes` bounds the linked IR size.
#[derive(Debug)]
pub struct Budget {
    edges: u64,
    max_edges: u64,
    states: u64,
    max_states: u64,
    max_depth: u64,
}

impl Budget {
    /// A budget from the explicit resource policy.
    #[must_use]
    pub fn new(max_token_lattice_edges: u64, max_parse_states: u64, max_scope_depth: u64) -> Self {
        Self {
            edges: 0,
            max_edges: max_token_lattice_edges,
            states: 0,
            max_states: max_parse_states,
            max_depth: max_scope_depth,
        }
    }

    /// The configured nesting limit.
    #[must_use]
    pub const fn max_depth(&self) -> u64 {
        self.max_depth
    }

    /// Check one nesting depth against `max_scope_depth`; `phase` names the
    /// nesting kind in the diagnostic.
    pub fn depth(&self, depth: u64, phase: &str) -> Result<(), Diagnostic> {
        depth_check(depth, self.max_depth, phase)
    }

    /// Count one lattice edge.
    pub fn edge(&mut self) -> Result<(), Diagnostic> {
        self.edges = self.edges.saturating_add(1);
        if self.edges > self.max_edges {
            return Err(Diagnostic::new(
                code!("LLS8002"),
                format!(
                    "max_token_lattice_edges exceeded: configured {}",
                    self.max_edges
                ),
            ));
        }
        Ok(())
    }

    /// Count one parse state.
    pub fn state(&mut self) -> Result<(), Diagnostic> {
        self.states = self.states.saturating_add(1);
        if self.states > self.max_states {
            return Err(Diagnostic::new(
                code!("LLS8002"),
                format!("max_parse_states exceeded: configured {}", self.max_states),
            ));
        }
        Ok(())
    }
}

/// The shared depth check (§25.5): nesting deeper than `max_scope_depth` is
/// `LLS8002` naming the limit, its configured value, and the phase.
pub fn depth_check(depth: u64, max_depth: u64, phase: &str) -> Result<(), Diagnostic> {
    if depth > max_depth {
        return Err(Diagnostic::new(
            code!("LLS8002"),
            format!("max_scope_depth exceeded in phase {phase}: configured {max_depth}, nesting depth {depth}"),
        ));
    }
    Ok(())
}

/// One token of the text channel: a non-whitespace atom position or one
/// complete mathematical island.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TextToken {
    /// A non-whitespace atom at this index.
    Atom(usize),
    /// A math island: the delimiting control atoms and the inner atom range.
    Island {
        /// Index of the opening `\(` or `\[`.
        open: usize,
        /// Inner range start (inclusive).
        inner_start: usize,
        /// Inner range end (exclusive).
        inner_end: usize,
        /// Index of the closing control.
        close: usize,
        /// Was this a display island `\[...\]`?
        display: bool,
    },
}

impl TextToken {
    /// The first atom index of this token.
    #[must_use]
    pub fn first_atom(&self) -> usize {
        match self {
            Self::Atom(index) => *index,
            Self::Island { open, .. } => *open,
        }
    }

    /// The last atom index (inclusive) of this token.
    #[must_use]
    pub fn last_atom(&self) -> usize {
        match self {
            Self::Atom(index) => *index,
            Self::Island { close, .. } => *close,
        }
    }
}

/// Tokenize an atom range into the text-channel view: whitespace dropped,
/// islands folded (§15.5). Dollar delimiters are forbidden; an unmatched
/// island delimiter is a parse failure.
pub fn text_tokens(
    path: &str,
    atoms: &[Atom],
    start: usize,
    end: usize,
) -> Result<Vec<TextToken>, Diagnostic> {
    let mut tokens = Vec::new();
    let mut index = start;
    while index < end {
        let atom = &atoms[index];
        match atom.class {
            AtomClass::Whitespace => {
                index += 1;
            }
            AtomClass::AsciiSymbol if atom.text == "$" => {
                return Err(Diagnostic::new(
                    code!("LLP2001"),
                    "dollar math delimiters are forbidden; use \\( ... \\) or \\[ ... \\]",
                )
                .with_span(atom.span(path)));
            }
            AtomClass::Control if atom.text == "\\(" || atom.text == "\\[" => {
                let display = atom.text == "\\[";
                let closer = if display { "\\]" } else { "\\)" };
                let mut scan = index + 1;
                while scan < end {
                    let candidate = &atoms[scan];
                    if candidate.class == AtomClass::Control && candidate.text == closer {
                        break;
                    }
                    if candidate.class == AtomClass::Control
                        && (candidate.text == "\\(" || candidate.text == "\\[")
                    {
                        return Err(Diagnostic::new(
                            code!("LLL1006"),
                            "mathematical islands do not nest",
                        )
                        .with_span(candidate.span(path)));
                    }
                    scan += 1;
                }
                if scan >= end {
                    return Err(Diagnostic::new(
                        code!("LLL1006"),
                        format!("unclosed mathematical island; expected `{closer}`"),
                    )
                    .with_span(atom.span(path)));
                }
                tokens.push(TextToken::Island {
                    open: index,
                    inner_start: index + 1,
                    inner_end: scan,
                    close: scan,
                    display,
                });
                index = scan + 1;
            }
            AtomClass::Control if atom.text == "\\)" || atom.text == "\\]" => {
                return Err(Diagnostic::new(
                    code!("LLL1006"),
                    format!("`{}` closes no mathematical island", atom.text),
                )
                .with_span(atom.span(path)));
            }
            _ => {
                tokens.push(TextToken::Atom(index));
                index += 1;
            }
        }
    }
    Ok(tokens)
}
