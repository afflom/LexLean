//! The mathematical-island grammar (SPEC.md §15.5): a Pratt parser over the
//! declared precedence scale `0..255`. Juxtaposition is never application,
//! braces do not group, and every operator's precedence and associativity
//! come from its glossary entry. Lexical alternatives stay embedded as
//! candidate sets; conservative elaboration selects uniquely or rejects
//! (§14.4).

use std::collections::{BTreeMap, BTreeSet};

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
        /// The call's own opening parenthesis atom.
        open: usize,
        /// The call's own closing parenthesis atom.
        close: usize,
        /// The call's own top-level argument-separating comma atoms, in
        /// source order. Parentheses and commas inside the arguments belong
        /// to those arguments (I1: every atom has exactly one origin).
        commas: Vec<usize>,
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

struct MathParser<'a, 'b> {
    path: &'a str,
    atoms: &'a [Atom],
    end: usize,
    at: usize,
    closure: &'a Closure,
    visible: &'a BTreeSet<String>,
    segmentation: &'b mut Segmentation,
}

/// The token-lattice branch record of one parse pass (§14.1). A leaf
/// position whose glossary forms and composed identifier disagree on the
/// covered extent is a lattice branch, not a decision: this pass takes the
/// extent `chosen` names for it, or the shortest one, and records the
/// position with every extent available there. The caller re-parses under
/// each recorded alternative, so the covers are chosen by which of them
/// link (§14.4) and never by which form the lattice happened to list first.
#[derive(Debug, Default)]
struct Segmentation {
    chosen: BTreeMap<usize, usize>,
    met: Vec<(usize, Vec<usize>)>,
}

type MResult<T> = Result<T, Diagnostic>;

/// One operator occurrence with its shared profile.
struct OpMatch {
    candidates: Vec<FormRef>,
    op_atoms: AtomRange,
    end: usize,
    /// Widened from the declared `u8` so `precedence + 1` at 255 never
    /// overflows (§15.5).
    precedence: u16,
    associativity: Option<Associativity>,
    frame: Frame,
}

impl<'a> MathParser<'a, '_> {
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
        let matches = budget.edges_at(
            self.closure,
            self.atoms,
            self.visible,
            self.at,
            Channel::Math,
        )?;
        let mut infix_like: Vec<(FormRef, usize, u16, Option<Associativity>, Frame)> = Vec::new();
        for (reference, match_end) in matches {
            let Some((entry, _)) = self.closure.form(&reference) else {
                continue;
            };
            if matches!(entry.frame, Frame::Infix | Frame::Postfix) && match_end <= self.end {
                infix_like.push((
                    reference,
                    match_end,
                    u16::from(entry.precedence.unwrap_or(0)),
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
    fn primary(&mut self, budget: &mut Budget, depth: u64) -> MResult<MathAst> {
        budget.state()?;
        if let Err(diagnostic) = budget.depth(depth, "parse (mathematical grouping)") {
            let span = self.span_here();
            return Err(diagnostic.with_span(span));
        }
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
                let inner = self.expression(budget, 0, depth.saturating_add(1))?;
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
                let matches = budget.edges_at(
                    self.closure,
                    self.atoms,
                    self.visible,
                    self.at,
                    Channel::Math,
                )?;
                let mut prefix: Vec<(FormRef, usize, u16)> = Vec::new();
                let mut leaf: Vec<(FormRef, usize)> = Vec::new();
                for (reference, match_end) in matches {
                    let Some((entry, _)) = self.closure.form(&reference) else {
                        continue;
                    };
                    match entry.frame {
                        Frame::Prefix if match_end <= self.end => {
                            prefix.push((
                                reference,
                                match_end,
                                u16::from(entry.precedence.unwrap_or(0)),
                            ));
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
                        let operand =
                            self.expression(budget, profile.1, depth.saturating_add(1))?;
                        return self.postfix_calls(
                            budget,
                            depth,
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
                // Different-length leaf matches at one position are
                // lattice alternatives, not a decision to make here
                // (§14.1): this pass covers one extent and records the
                // rest for the enclosing enumeration.
                let identifier = if atom.class == AtomClass::Word {
                    compose_identifier(self.atoms, self.at).filter(|(_, end)| *end <= self.end)
                } else {
                    None
                };
                let mut ends: Vec<usize> = leaf.iter().map(|(_, end)| *end).collect();
                ends.extend(identifier.iter().map(|(_, end)| *end));
                ends.sort_unstable();
                ends.dedup();
                let Some(&shortest) = ends.first() else {
                    return Err(Diagnostic::new(
                        code!("LLL1004"),
                        format!("unknown atom `{}` in a mathematical island", atom.text),
                    )
                    .with_span(atom.span(self.path)));
                };
                let end_atom = match self.segmentation.chosen.get(&start) {
                    Some(chosen) if ends.contains(chosen) => *chosen,
                    _ => shortest,
                };
                if ends.len() > 1 {
                    self.segmentation.met.push((start, ends));
                }
                let mut kinds: Vec<LeafKind> = leaf
                    .into_iter()
                    .filter(|(_, end)| *end == end_atom)
                    .map(|(reference, _)| LeafKind::Form(reference))
                    .collect();
                if let Some((text, end)) = identifier {
                    if end == end_atom {
                        kinds.push(LeafKind::Ident(text));
                    }
                }
                self.at = end_atom;
                MathAst::Leaf {
                    kinds,
                    atoms: (start, end_atom),
                }
            }
        };
        self.postfix_calls(budget, depth, base)
    }

    /// Explicit call syntax after a primary: `head(a, b)`.
    fn postfix_calls(
        &mut self,
        budget: &mut Budget,
        depth: u64,
        mut base: MathAst,
    ) -> MResult<MathAst> {
        while let Some(atom) = self.peek() {
            if atom.class == AtomClass::Delimiter && atom.text == "(" {
                // A call only when the head can be applied; a grouping
                // parenthesis never follows a completed primary because
                // juxtaposition is never application (§15.5).
                let call_start = base.atoms().0;
                let open = self.at;
                self.at += 1;
                let mut commas = Vec::new();
                let mut args = vec![self.expression(budget, 0, depth.saturating_add(1))?];
                let close;
                loop {
                    match self.peek() {
                        Some(separator)
                            if separator.class == AtomClass::AsciiSymbol
                                && separator.text == "," =>
                        {
                            commas.push(self.at);
                            self.at += 1;
                            args.push(self.expression(budget, 0, depth.saturating_add(1))?);
                        }
                        Some(close_atom)
                            if close_atom.class == AtomClass::Delimiter
                                && close_atom.text == ")" =>
                        {
                            close = self.at;
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
                    open,
                    close,
                    commas,
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

    /// One Pratt expression at `min_bp`; `depth` counts the grammatical
    /// nesting (grouping, call arguments, prefix operands, and right-nested
    /// infix operands) against `max_scope_depth` (§25.5).
    fn expression(&mut self, budget: &mut Budget, min_bp: u16, depth: u64) -> MResult<MathAst> {
        budget.state()?;
        let mut lhs = self.primary(budget, depth)?;
        let mut last_nonassoc: Option<u16> = None;
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
                        Some(Associativity::Left) => (op.precedence.saturating_add(1), None),
                        Some(Associativity::Right) => (op.precedence, None),
                        Some(Associativity::None) | None => {
                            (op.precedence.saturating_add(1), Some(op.precedence))
                        }
                    };
                    self.at = op.end;
                    let rhs = self.expression(budget, next_min, depth.saturating_add(1))?;
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

/// Parse one mathematical island's inner atom range under every
/// segmentation the token lattice admits (§14.1): the returned parses are
/// the distinct complete covers of the range, in a deterministic order, and
/// the caller decides between them by linking (§14.4). Enumeration is a
/// worklist over the branch points one pass met, and every pass is charged
/// against `max_parse_states` and the module's shared lattice-edge budget
/// (§25.5), so an island with many branch points is a named limit failure
/// and never unbounded work.
pub fn parse_math(
    path: &str,
    atoms: &[Atom],
    range: AtomRange,
    closure: &Closure,
    visible: &BTreeSet<String>,
    budget: &mut Budget,
) -> Result<Vec<MathAst>, Diagnostic> {
    let mut queue: Vec<BTreeMap<usize, usize>> = vec![BTreeMap::new()];
    let mut enqueued: BTreeSet<Vec<(usize, usize)>> = BTreeSet::new();
    enqueued.insert(Vec::new());
    let mut covers: Vec<MathAst> = Vec::new();
    // The first pass is the one every unambiguous island takes, so its
    // failure is the one an unambiguous island reports.
    let mut failure: Option<Diagnostic> = None;
    while let Some(chosen) = queue.pop() {
        let mut segmentation = Segmentation {
            chosen,
            met: Vec::new(),
        };
        match parse_cover(
            path,
            atoms,
            range,
            closure,
            visible,
            budget,
            &mut segmentation,
        ) {
            Ok(cover) => {
                if !covers.contains(&cover) {
                    covers.push(cover);
                }
            }
            Err(diagnostic) => {
                if failure.is_none() {
                    failure = Some(diagnostic);
                }
            }
        }
        for (position, ends) in &segmentation.met {
            if segmentation.chosen.contains_key(position) {
                continue;
            }
            // The pass above took the shortest extent; each other extent is
            // one more cover to try.
            for end in ends.iter().skip(1) {
                let mut next = segmentation.chosen.clone();
                next.insert(*position, *end);
                let key: Vec<(usize, usize)> = next.iter().map(|(at, end)| (*at, *end)).collect();
                if enqueued.insert(key) {
                    queue.push(next);
                }
            }
        }
    }
    match failure {
        Some(diagnostic) if covers.is_empty() => Err(diagnostic),
        _ if covers.is_empty() => Err(Diagnostic::new(
            code!("LLI9001"),
            "phase parse: the token lattice produced neither a cover nor a failure",
        )
        .with_span(crate::diagnostic::Span::whole_file(path))),
        _ => Ok(covers),
    }
}

/// One complete cover of `range` under the given segmentation choices.
fn parse_cover(
    path: &str,
    atoms: &[Atom],
    range: AtomRange,
    closure: &Closure,
    visible: &BTreeSet<String>,
    budget: &mut Budget,
    segmentation: &mut Segmentation,
) -> Result<MathAst, Diagnostic> {
    let mut parser = MathParser {
        path,
        atoms,
        end: range.1,
        at: range.0,
        closure,
        visible,
        segmentation,
    };
    let expression = parser.expression(budget, 0, 1)?;
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
            || !budget
                .edges_at(closure, atoms, visible, parser.at, Channel::Math)?
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
