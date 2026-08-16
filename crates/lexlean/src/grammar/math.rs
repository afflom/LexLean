//! The mathematical-island grammar (SPEC.md §15.5): a Pratt parser over the
//! declared precedence scale `0..255`. Juxtaposition is never application,
//! braces do not group, and every operator's precedence and associativity
//! come from its glossary entry. Lexical alternatives stay embedded as
//! candidate sets; conservative elaboration selects uniquely or rejects
//! (§14.4).

use std::collections::BTreeSet;

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::grammar::chart::Budget;
use crate::grammar::structural::AtomRange;
use crate::lexicon::entry::{Associativity, Channel, Frame};
use crate::lexicon::resolve::{Closure, FormRef};
use crate::source::atom::{Atom, AtomClass};
use crate::source::scan::compose_identifier;

/// One leaf interpretation candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeafKind {
    /// A composed identifier: a scoped local occurrence or binder spelling.
    Ident(String),
    /// A matched glossary form with an atom frame or a call head.
    Form(FormRef),
}

/// A parsed mathematical expression with embedded lexical alternatives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MathAst {
    /// A numeral (§15.5): the core numeric constructor, no default type.
    Numeral {
        /// The digits.
        text: String,
        /// The atom range.
        atoms: AtomRange,
    },
    /// A leaf with its interpretation candidates.
    Leaf {
        /// The candidates, in deterministic order.
        kinds: Vec<LeafKind>,
        /// The atom range.
        atoms: AtomRange,
    },
    /// `\lexeme{package::entry}` (§14.3).
    Lexeme {
        /// The qualified entry text.
        qualified: String,
        /// The atom range including the control and braces.
        atoms: AtomRange,
    },
    /// `\reference{Module::component}` (§14.3).
    Reference {
        /// The module name.
        module: String,
        /// The component ID.
        component: String,
        /// The atom range including the control and braces.
        atoms: AtomRange,
    },
    /// Explicit call syntax `f(a, b)` (§15.5).
    Call {
        /// The applied head.
        head: Box<MathAst>,
        /// The arguments.
        args: Vec<MathAst>,
        /// The full atom range.
        atoms: AtomRange,
    },
    /// A prefix operator application.
    Prefix {
        /// Operator candidates sharing one precedence profile.
        candidates: Vec<FormRef>,
        /// The operator atom range.
        op_atoms: AtomRange,
        /// The operand.
        arg: Box<MathAst>,
    },
    /// A postfix operator application.
    Postfix {
        /// Operator candidates.
        candidates: Vec<FormRef>,
        /// The operator atom range.
        op_atoms: AtomRange,
        /// The operand.
        arg: Box<MathAst>,
    },
    /// An infix operator application.
    Infix {
        /// Operator candidates sharing one precedence profile.
        candidates: Vec<FormRef>,
        /// The operator atom range.
        op_atoms: AtomRange,
        /// The left operand.
        lhs: Box<MathAst>,
        /// The right operand.
        rhs: Box<MathAst>,
    },
    /// Explicit grouping parentheses.
    Paren {
        /// The grouped expression.
        inner: Box<MathAst>,
        /// The full atom range including both parentheses.
        atoms: AtomRange,
    },
}

impl MathAst {
    /// The covered atom range.
    #[must_use]
    pub fn atoms(&self) -> AtomRange {
        match self {
            Self::Numeral { atoms, .. }
            | Self::Leaf { atoms, .. }
            | Self::Lexeme { atoms, .. }
            | Self::Reference { atoms, .. }
            | Self::Call { atoms, .. }
            | Self::Paren { atoms, .. } => *atoms,
            Self::Prefix { op_atoms, arg, .. } => (op_atoms.0, arg.atoms().1),
            Self::Postfix { op_atoms, arg, .. } => (arg.atoms().0, op_atoms.1),
            Self::Infix { lhs, rhs, .. } => (lhs.atoms().0, rhs.atoms().1),
        }
    }
}

struct MathParser<'a> {
    path: &'a str,
    atoms: &'a [Atom],
    end: usize,
    at: usize,
    closure: &'a Closure,
    visible: &'a BTreeSet<String>,
}

type MResult<T> = Result<T, Diagnostic>;

/// One operator occurrence with its shared profile.
struct OpMatch {
    candidates: Vec<FormRef>,
    op_atoms: AtomRange,
    end: usize,
    precedence: u8,
    associativity: Option<Associativity>,
    frame: Frame,
}

impl<'a> MathParser<'a> {
    fn skip_ws(&mut self) {
        while self.at < self.end && self.atoms[self.at].class == AtomClass::Whitespace {
            self.at += 1;
        }
    }

    fn peek(&mut self) -> Option<&'a Atom> {
        self.skip_ws();
        if self.at < self.end {
            Some(&self.atoms[self.at])
        } else {
            None
        }
    }

    fn span_here(&mut self) -> crate::diagnostic::Span {
        match self.peek() {
            Some(atom) => atom.span(self.path),
            None => {
                let last = &self.atoms[self.end.saturating_sub(1)];
                last.span(self.path)
            }
        }
    }

    /// Group the operator matches at the cursor by frame. Distinct
    /// precedence profiles for one surface cannot be disambiguated without
    /// guessing, so they are rejected (I5: LexLean rejects rather than
    /// guesses).
    fn operator_at(&mut self, budget: &mut Budget) -> MResult<Option<OpMatch>> {
        self.skip_ws();
        if self.at >= self.end {
            return Ok(None);
        }
        let matches = self
            .closure
            .matches_at(self.atoms, self.at, Channel::Math, self.visible);
        let mut infix_like: Vec<(FormRef, usize, u8, Option<Associativity>, Frame)> = Vec::new();
        for (reference, match_end) in matches {
            budget.edge()?;
            let Some((entry, _)) = self.closure.form(&reference) else {
                continue;
            };
            if matches!(entry.frame, Frame::Infix | Frame::Postfix) && match_end <= self.end {
                infix_like.push((
                    reference,
                    match_end,
                    entry.precedence.unwrap_or(0),
                    entry.associativity,
                    entry.frame,
                ));
            }
        }
        if infix_like.is_empty() {
            return Ok(None);
        }
        let profile = (
            infix_like[0].1,
            infix_like[0].2,
            infix_like[0].3,
            infix_like[0].4,
        );
        if infix_like
            .iter()
            .any(|(_, e, p, a, f)| (*e, *p, *a, *f) != profile)
        {
            let span = self.span_here();
            return Err(Diagnostic::new(
                code!("LLP2002"),
                "operator candidates at this surface disagree on precedence, associativity, or frame; LexLean does not guess",
            )
            .with_span(span));
        }
        let op_atoms = (self.at, infix_like[0].1);
        Ok(Some(OpMatch {
            candidates: infix_like.into_iter().map(|(r, ..)| r).collect(),
            op_atoms,
            end: profile.0,
            precedence: profile.1,
            associativity: profile.2,
            frame: profile.3,
        }))
    }

    #[allow(clippy::too_many_lines)]
    fn primary(&mut self, budget: &mut Budget) -> MResult<MathAst> {
        budget.state()?;
        let Some(atom) = self.peek() else {
            let span = self.span_here();
            return Err(
                Diagnostic::new(code!("LLP2001"), "expected a mathematical expression")
                    .with_span(span),
            );
        };
        let start = self.at;
        let base = match (atom.class, atom.text.as_str()) {
            (AtomClass::Numeral, _) => {
                self.at += 1;
                MathAst::Numeral {
                    text: atom.text.clone(),
                    atoms: (start, start + 1),
                }
            }
            (AtomClass::Delimiter, "(") => {
                self.at += 1;
                let inner = self.expression(budget, 0)?;
                match self.peek() {
                    Some(close) if close.class == AtomClass::Delimiter && close.text == ")" => {
                        self.at += 1;
                        MathAst::Paren {
                            inner: Box::new(inner),
                            atoms: (start, self.at),
                        }
                    }
                    _ => {
                        let span = self.span_here();
                        return Err(Diagnostic::new(
                            code!("LLP2004"),
                            "unclosed grouping parenthesis",
                        )
                        .with_span(span));
                    }
                }
            }
            (AtomClass::Delimiter, "{" | "}") => {
                return Err(Diagnostic::new(
                    code!("LLP2004"),
                    "braces do not group mathematical terms",
                )
                .with_span(atom.span(self.path)));
            }
            (AtomClass::Control, "\\lexeme") => {
                self.at += 1;
                let (qualified, end) = self.metadata_braces()?;
                MathAst::Lexeme {
                    qualified,
                    atoms: (start, end),
                }
            }
            (AtomClass::Control, "\\reference") => {
                self.at += 1;
                let (text, end) = self.metadata_braces()?;
                let Some((module, component)) = text.split_once("::") else {
                    return Err(Diagnostic::new(
                        code!("LLR3005"),
                        format!("`{text}` is not a `Module::component` reference"),
                    )
                    .with_span(atom.span(self.path)));
                };
                MathAst::Reference {
                    module: module.to_owned(),
                    component: component.to_owned(),
                    atoms: (start, end),
                }
            }
            _ => {
                // Prefix operator, glossary form, or composed identifier.
                let matches =
                    self.closure
                        .matches_at(self.atoms, self.at, Channel::Math, self.visible);
                let mut prefix: Vec<(FormRef, usize, u8)> = Vec::new();
                let mut leaf: Vec<(FormRef, usize)> = Vec::new();
                for (reference, match_end) in matches {
                    budget.edge()?;
                    let Some((entry, _)) = self.closure.form(&reference) else {
                        continue;
                    };
                    match entry.frame {
                        Frame::Prefix if match_end <= self.end => {
                            prefix.push((reference, match_end, entry.precedence.unwrap_or(0)));
                        }
                        Frame::Atom | Frame::Call if match_end <= self.end => {
                            leaf.push((reference, match_end));
                        }
                        _ => {}
                    }
                }
                if !prefix.is_empty() {
                    let profile = (prefix[0].1, prefix[0].2);
                    if prefix.iter().any(|(_, e, p)| (*e, *p) != profile) {
                        return Err(Diagnostic::new(
                            code!("LLP2002"),
                            "prefix candidates disagree on their profile; LexLean does not guess",
                        )
                        .with_span(atom.span(self.path)));
                    }
                    if leaf.is_empty() {
                        let op_atoms = (self.at, profile.0);
                        self.at = profile.0;
                        let operand = self.expression(budget, profile.1)?;
                        return self.postfix_calls(
                            budget,
                            MathAst::Prefix {
                                candidates: prefix.into_iter().map(|(r, ..)| r).collect(),
                                op_atoms,
                                arg: Box::new(operand),
                            },
                        );
                    }
                    return Err(Diagnostic::new(
                        code!("LLP2002"),
                        "this surface is both a prefix operator and a leaf; LexLean does not guess",
                    )
                    .with_span(atom.span(self.path)));
                }
                let mut kinds: Vec<LeafKind> = Vec::new();
                let mut leaf_end = None;
                for (reference, match_end) in leaf {
                    match leaf_end {
                        None => leaf_end = Some(match_end),
                        Some(existing) if existing == match_end => {}
                        Some(_) => {
                            // Different-length leaf matches at one position:
                            // segmentation stays open; the lattice keeps
                            // both only if the parse can continue, which a
                            // single-token leaf grammar cannot. Reject as
                            // ambiguity rather than guess.
                            return Err(Diagnostic::new(
                                code!("LLP2002"),
                                "ambiguous lexical segmentation in a mathematical island",
                            )
                            .with_span(atom.span(self.path)));
                        }
                    }
                    kinds.push(LeafKind::Form(reference));
                }
                if atom.class == AtomClass::Word {
                    if let Some((text, end_atom)) = compose_identifier(self.atoms, self.at) {
                        if end_atom <= self.end {
                            match leaf_end {
                                Some(existing) if existing != end_atom => {
                                    return Err(Diagnostic::new(
                                        code!("LLP2002"),
                                        "ambiguous lexical segmentation in a mathematical island",
                                    )
                                    .with_span(atom.span(self.path)));
                                }
                                _ => {}
                            }
                            leaf_end = Some(leaf_end.unwrap_or(end_atom));
                            kinds.push(LeafKind::Ident(text));
                        }
                    }
                }
                let Some(end_atom) = leaf_end else {
                    return Err(Diagnostic::new(
                        code!("LLL1004"),
                        format!("unknown atom `{}` in a mathematical island", atom.text),
                    )
                    .with_span(atom.span(self.path)));
                };
                self.at = end_atom;
                MathAst::Leaf {
                    kinds,
                    atoms: (start, end_atom),
                }
            }
        };
        self.postfix_calls(budget, base)
    }

    /// Explicit call syntax after a primary: `head(a, b)`.
    fn postfix_calls(&mut self, budget: &mut Budget, mut base: MathAst) -> MResult<MathAst> {
        while let Some(atom) = self.peek() {
            if atom.class == AtomClass::Delimiter && atom.text == "(" {
                // A call only when the head can be applied; a grouping
                // parenthesis never follows a completed primary because
                // juxtaposition is never application (§15.5).
                let call_start = base.atoms().0;
                self.at += 1;
                let mut args = vec![self.expression(budget, 0)?];
                loop {
                    match self.peek() {
                        Some(separator)
                            if separator.class == AtomClass::AsciiSymbol
                                && separator.text == "," =>
                        {
                            self.at += 1;
                            args.push(self.expression(budget, 0)?);
                        }
                        Some(close) if close.class == AtomClass::Delimiter && close.text == ")" => {
                            self.at += 1;
                            break;
                        }
                        _ => {
                            let span = self.span_here();
                            return Err(Diagnostic::new(
                                code!("LLP2004"),
                                "expected `,` or `)` in a call argument list",
                            )
                            .with_span(span));
                        }
                    }
                }
                base = MathAst::Call {
                    head: Box::new(base),
                    args,
                    atoms: (call_start, self.at),
                };
            } else {
                break;
            }
        }
        Ok(base)
    }

    fn metadata_braces(&mut self) -> MResult<(String, usize)> {
        match self.peek() {
            Some(open) if open.class == AtomClass::Delimiter && open.text == "{" => {
                self.at += 1;
            }
            _ => {
                let span = self.span_here();
                return Err(Diagnostic::new(code!("LLP2003"), "expected `{`").with_span(span));
            }
        }
        let mut text = String::new();
        loop {
            let Some(atom) = self.atoms.get(self.at).filter(|_| self.at < self.end) else {
                let span = self.span_here();
                return Err(
                    Diagnostic::new(code!("LLP2003"), "unclosed `{` argument").with_span(span)
                );
            };
            match (atom.class, atom.text.as_str()) {
                (AtomClass::Delimiter, "}") => {
                    self.at += 1;
                    return Ok((text, self.at));
                }
                (AtomClass::Whitespace, _) => self.at += 1,
                _ => {
                    text.push_str(&atom.text);
                    self.at += 1;
                }
            }
        }
    }

    fn expression(&mut self, budget: &mut Budget, min_bp: u8) -> MResult<MathAst> {
        budget.state()?;
        let mut lhs = self.primary(budget)?;
        let mut last_nonassoc: Option<u8> = None;
        while let Some(op) = self.operator_at(budget)? {
            if op.precedence < min_bp {
                break;
            }
            match op.frame {
                Frame::Postfix => {
                    self.at = op.end;
                    lhs = MathAst::Postfix {
                        candidates: op.candidates,
                        op_atoms: op.op_atoms,
                        arg: Box::new(lhs),
                    };
                }
                Frame::Infix => {
                    if last_nonassoc == Some(op.precedence) {
                        let span = self.span_here();
                        return Err(Diagnostic::new(
                            code!("LLP2004"),
                            "a nonassociative chain requires explicit parentheses",
                        )
                        .with_span(span));
                    }
                    let (next_min, remember_nonassoc) = match op.associativity {
                        Some(Associativity::Left) => (op.precedence + 1, None),
                        Some(Associativity::Right) => (op.precedence, None),
                        Some(Associativity::None) | None => {
                            (op.precedence + 1, Some(op.precedence))
                        }
                    };
                    self.at = op.end;
                    let rhs = self.expression(budget, next_min)?;
                    last_nonassoc = remember_nonassoc;
                    lhs = MathAst::Infix {
                        candidates: op.candidates,
                        op_atoms: op.op_atoms,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    };
                }
                _ => break,
            }
        }
        Ok(lhs)
    }
}

/// Parse one mathematical island's inner atom range.
pub fn parse_math(
    path: &str,
    atoms: &[Atom],
    range: AtomRange,
    closure: &Closure,
    visible: &BTreeSet<String>,
    budget: &mut Budget,
) -> Result<MathAst, Diagnostic> {
    let mut parser = MathParser {
        path,
        atoms,
        end: range.1,
        at: range.0,
        closure,
        visible,
    };
    let expression = parser.expression(budget, 0)?;
    parser.skip_ws();
    if parser.at < parser.end {
        let atom = &atoms[parser.at];
        // The exact unknown-atom diagnosis (I2, §12.2): an atom that no
        // visible math form, local identifier, numeral, or grouping
        // delimiter can ever cover is unknown, not merely misplaced.
        let bindable = matches!(
            atom.class,
            AtomClass::Word | AtomClass::Numeral | AtomClass::Delimiter | AtomClass::Whitespace
        ) || atom.text == ","
            || !closure
                .matches_at(atoms, parser.at, Channel::Math, visible)
                .is_empty();
        if !bindable {
            return Err(Diagnostic::new(
                code!("LLL1004"),
                format!("unknown atom `{}` in a mathematical island", atom.text),
            )
            .with_span(atom.span(path)));
        }
        return Err(Diagnostic::new(
            code!("LLP2004"),
            format!("unexpected `{}` after the expression", atom.text),
        )
        .with_span(atom.span(path)));
    }
    Ok(expression)
}
