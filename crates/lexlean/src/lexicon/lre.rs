//! LexLean Rendering Expressions (SPEC.md §13.9): the only way a glossary
//! entry influences canonical visible output. Raw TeX strings do not exist.
//!
//! The parser is depth-bounded by the configured `max_scope_depth` (see the
//! `lse` module documentation for the mapping) and every walker is
//! iterative.

use crate::lexicon::lse::{read_tree, Node, ParseError, QualifiedId};

/// A parsed render expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Render {
    /// `(form qualified-id form-id)`: another entry's form.
    Form {
        /// The referenced entry.
        entry: QualifiedId,
        /// The referenced form ID.
        form: String,
    },
    /// `(self-form form-id)`: one of this entry's own forms.
    SelfForm(String),
    /// `(slot n)`: an explicit surface argument.
    Slot(u32),
    /// `(seq ...)`.
    Seq(Vec<Render>),
    /// `(space)`.
    Space,
    /// `(token renderer-token-id)`.
    Token(String),
    /// `(group r)`: a brace group.
    Group(Box<Render>),
    /// `(paren r)`.
    Paren(Box<Render>),
    /// `(bracket r)`.
    Bracket(Box<Render>),
    /// `(sub base script)`.
    Sub(Box<Render>, Box<Render>),
    /// `(sup base script)`.
    Sup(Box<Render>, Box<Render>),
    /// `(frac numerator denominator)`.
    Frac(Box<Render>, Box<Render>),
    /// `(operator-name ascii-identifier)`.
    OperatorName(String),
}

/// `[A-Za-z][A-Za-z0-9_]*` (§13.9).
#[must_use]
pub fn is_operator_name(text: &str) -> bool {
    let bytes = text.as_bytes();
    matches!(bytes.first(), Some(b) if b.is_ascii_alphabetic())
        && bytes[1..]
            .iter()
            .all(|b| b.is_ascii_alphanumeric() || *b == b'_')
}

/// A renderer-token ID: `[a-z][a-z0-9-]*`.
#[must_use]
pub fn is_token_id(text: &str) -> bool {
    let bytes = text.as_bytes();
    matches!(bytes.first(), Some(b) if b.is_ascii_lowercase())
        && bytes[1..]
            .iter()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || *b == b'-')
}

/// A form ID: the local form identifier grammar, `[a-z][a-z0-9-]*`.
#[must_use]
pub fn is_form_id(text: &str) -> bool {
    is_token_id(text)
}

fn syntax(message: impl Into<String>) -> ParseError {
    ParseError::Syntax(message.into())
}

fn atom_of(node: &Node, what: &str) -> Result<String, ParseError> {
    match node {
        Node::Atom(text) => Ok(text.clone()),
        other => Err(syntax(format!(
            "expected {what}, found {}",
            other.describe()
        ))),
    }
}

/// Convert a generic tree into a render expression, iteratively.
fn render_of(root: &Node) -> Result<Render, ParseError> {
    enum Work<'a> {
        Visit(&'a Node),
        Build(&'a str, usize),
    }
    let mut work = vec![Work::Visit(root)];
    let mut values: Vec<Render> = Vec::new();
    while let Some(item) = work.pop() {
        match item {
            Work::Visit(node) => {
                let Node::List(items) = node else {
                    return Err(syntax(format!("expected `(`, found {}", node.describe())));
                };
                let Some(Node::Atom(head)) = items.first() else {
                    return Err(syntax("expected an LRE form"));
                };
                let arguments = &items[1..];
                match head.as_str() {
                    "form" => match arguments {
                        [entry, form] => {
                            let entry = QualifiedId::parse(&atom_of(entry, "a qualified ID")?)?;
                            let form = atom_of(form, "a form ID")?;
                            if !is_form_id(&form) {
                                return Err(syntax(format!("`{form}` is not a form ID")));
                            }
                            values.push(Render::Form { entry, form });
                        }
                        _ => {
                            return Err(syntax("a form reference is `(form qualified-id form-id)`"))
                        }
                    },
                    "self-form" => match arguments {
                        [form] => {
                            let form = atom_of(form, "a form ID")?;
                            if !is_form_id(&form) {
                                return Err(syntax(format!("`{form}` is not a form ID")));
                            }
                            values.push(Render::SelfForm(form));
                        }
                        _ => return Err(syntax("a self form is `(self-form form-id)`")),
                    },
                    "slot" => match arguments {
                        [digits] => {
                            // A slot index is a canonical decimal: digits only,
                            // no sign, no redundant leading zero (§13.8).
                            let digits = atom_of(digits, "a slot index")?;
                            let value = crate::lexicon::lse::parse_decimal(&digits)
                                .map_err(|_| syntax(format!("`{digits}` is not a slot index")))?;
                            let index = u32::try_from(value)
                                .map_err(|_| syntax(format!("`{digits}` is not a slot index")))?;
                            values.push(Render::Slot(index));
                        }
                        _ => return Err(syntax("a slot is `(slot decimal)`")),
                    },
                    "space" => {
                        if !arguments.is_empty() {
                            return Err(syntax("`(space)` takes no operand"));
                        }
                        values.push(Render::Space);
                    }
                    "token" => match arguments {
                        [id] => {
                            let id = atom_of(id, "a renderer-token ID")?;
                            if !is_token_id(&id) {
                                return Err(syntax(format!("`{id}` is not a renderer-token ID")));
                            }
                            values.push(Render::Token(id));
                        }
                        _ => return Err(syntax("a token is `(token renderer-token-id)`")),
                    },
                    "operator-name" => match arguments {
                        [name] => {
                            let name = atom_of(name, "an operator name")?;
                            if !is_operator_name(&name) {
                                return Err(syntax(format!("`{name}` is not an operator name")));
                            }
                            values.push(Render::OperatorName(name));
                        }
                        _ => {
                            return Err(syntax("an operator name is `(operator-name identifier)`"))
                        }
                    },
                    "seq" => {
                        if arguments.is_empty() {
                            return Err(syntax("`seq` has at least one item"));
                        }
                        work.push(Work::Build(head, arguments.len()));
                        for argument in arguments.iter().rev() {
                            work.push(Work::Visit(argument));
                        }
                    }
                    "group" | "paren" | "bracket" => {
                        if arguments.len() != 1 {
                            return Err(syntax(format!("`{head}` takes exactly one operand")));
                        }
                        work.push(Work::Build(head, 1));
                        work.push(Work::Visit(&arguments[0]));
                    }
                    "sub" | "sup" | "frac" => {
                        if arguments.len() != 2 {
                            return Err(syntax(format!("`{head}` takes exactly two operands")));
                        }
                        work.push(Work::Build(head, 2));
                        work.push(Work::Visit(&arguments[1]));
                        work.push(Work::Visit(&arguments[0]));
                    }
                    other => return Err(syntax(format!("`{other}` is not an LRE form"))),
                }
            }
            Work::Build(head, count) => {
                let start = values.len().saturating_sub(count);
                let mut parts: Vec<Render> = values.drain(start..).collect();
                let built = match head {
                    "seq" => Render::Seq(parts),
                    "group" | "paren" | "bracket" => {
                        let inner = Box::new(parts.pop().ok_or_else(|| syntax("missing operand"))?);
                        match head {
                            "group" => Render::Group(inner),
                            "paren" => Render::Paren(inner),
                            _ => Render::Bracket(inner),
                        }
                    }
                    _ => {
                        let second =
                            Box::new(parts.pop().ok_or_else(|| syntax("missing operand"))?);
                        let first = Box::new(parts.pop().ok_or_else(|| syntax("missing operand"))?);
                        match head {
                            "sub" => Render::Sub(first, second),
                            "sup" => Render::Sup(first, second),
                            _ => Render::Frac(first, second),
                        }
                    }
                };
                values.push(built);
            }
        }
    }
    match (values.pop(), values.is_empty()) {
        (Some(render), true) => Ok(render),
        _ => Err(syntax("malformed render expression")),
    }
}

/// Parse one complete render expression, nesting bounded by `max_depth`
/// (the configured `max_scope_depth`). Reader and conversion are iterative.
pub fn parse(text: &str, max_depth: u64) -> Result<Render, ParseError> {
    let tree = read_tree(text, max_depth)?;
    render_of(&tree)
}

impl Render {
    /// Every slot index used, in occurrence order.
    #[must_use]
    pub fn slots(&self) -> Vec<u32> {
        let mut out = Vec::new();
        self.walk(&mut |render| {
            if let Self::Slot(index) = render {
                out.push(*index);
            }
        });
        out
    }

    /// Every renderer token referenced.
    #[must_use]
    pub fn tokens(&self) -> Vec<String> {
        let mut out = Vec::new();
        self.walk(&mut |render| {
            if let Self::Token(id) = render {
                out.push(id.clone());
            }
        });
        out
    }

    /// Every `(form entry form)` reference.
    #[must_use]
    pub fn form_refs(&self) -> Vec<(QualifiedId, String)> {
        let mut out = Vec::new();
        self.walk(&mut |render| {
            if let Self::Form { entry, form } = render {
                out.push((entry.clone(), form.clone()));
            }
        });
        out
    }

    /// Every `(self-form id)` reference.
    #[must_use]
    pub fn self_form_refs(&self) -> Vec<String> {
        let mut out = Vec::new();
        self.walk(&mut |render| {
            if let Self::SelfForm(id) = render {
                out.push(id.clone());
            }
        });
        out
    }

    /// Every operator name.
    #[must_use]
    pub fn operator_names(&self) -> Vec<String> {
        let mut out = Vec::new();
        self.walk(&mut |render| {
            if let Self::OperatorName(name) = render {
                out.push(name.clone());
            }
        });
        out
    }

    /// The well-formedness of `sub`, `sup`, and `frac` operands (§13.9): a
    /// script or fraction operand must render something — it cannot be a
    /// bare `(space)`, and a `seq` operand cannot consist of spaces only —
    /// and a script must not itself be a bare script (`x_{y_z}` needs an
    /// explicit group). Returns the first offending operand.
    #[must_use]
    pub fn script_operand_error(&self) -> Option<String> {
        fn renders_nothing(render: &Render) -> bool {
            match render {
                Render::Space => true,
                Render::Seq(items) => items.iter().all(renders_nothing),
                _ => false,
            }
        }
        let mut problem = None;
        self.walk(&mut |render| {
            if problem.is_some() {
                return;
            }
            let (name, operands): (&str, [&Render; 2]) = match render {
                Self::Sub(a, b) => ("sub", [a, b]),
                Self::Sup(a, b) => ("sup", [a, b]),
                Self::Frac(a, b) => ("frac", [a, b]),
                _ => return,
            };
            for operand in operands {
                if renders_nothing(operand) {
                    problem = Some(format!("`{name}` operand renders nothing"));
                    return;
                }
                if name != "frac" && matches!(operand, Self::Sub(..) | Self::Sup(..)) {
                    problem = Some(format!(
                        "`{name}` operand is a bare script; wrap nested scripts in `(group ...)`"
                    ));
                    return;
                }
            }
        });
        problem
    }

    /// Pre-order visit of every node, iterative.
    fn walk(&self, visit: &mut impl FnMut(&Render)) {
        let mut stack: Vec<&Render> = vec![self];
        while let Some(render) = stack.pop() {
            visit(render);
            match render {
                Self::Seq(items) => {
                    for item in items.iter().rev() {
                        stack.push(item);
                    }
                }
                Self::Group(inner) | Self::Paren(inner) | Self::Bracket(inner) => {
                    stack.push(inner);
                }
                Self::Sub(a, b) | Self::Sup(a, b) | Self::Frac(a, b) => {
                    stack.push(b);
                    stack.push(a);
                }
                Self::Form { .. }
                | Self::SelfForm(_)
                | Self::Slot(_)
                | Self::Space
                | Self::Token(_)
                | Self::OperatorName(_) => {}
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_every_production() {
        let text = "(seq (form lexlean.core::the the-l) (space) (self-form x) (slot 0) (token plus) (group (slot 1)) (paren (slot 2)) (bracket (slot 3)) (sub (slot 4) (slot 5)) (sup (slot 6) (slot 7)) (frac (slot 8) (slot 9)) (operator-name succ_1))";
        let render = parse(text, 64).expect("parses");
        assert_eq!(render.slots(), (0..10).collect::<Vec<u32>>());
        assert_eq!(render.tokens(), vec!["plus".to_owned()]);
        assert_eq!(render.self_form_refs(), vec!["x".to_owned()]);
        assert_eq!(render.operator_names(), vec!["succ_1".to_owned()]);
        assert_eq!(render.form_refs().len(), 1);
        assert_eq!(render.script_operand_error(), None);
    }

    #[test]
    fn slot_indices_are_canonical_decimals() {
        assert!(parse("(slot 0)", 8).is_ok());
        assert!(parse("(slot 01)", 8).is_err());
        assert!(parse("(slot +1)", 8).is_err());
        assert!(parse("(slot -1)", 8).is_err());
        assert!(parse("(slot 99999999999)", 8).is_err());
    }

    #[test]
    fn rejects_raw_material() {
        assert!(parse("(raw \\\\relax)", 8).is_err());
        assert!(parse("(token \\relax)", 8).is_err());
        assert!(parse("(operator-name a-b)", 8).is_err());
        assert!(parse("(seq)", 8).is_err());
        assert!(parse("(slot 0) (slot 1)", 8).is_err());
        assert!(parse("(self-form Bad)", 8).is_err());
    }

    #[test]
    fn depth_is_bounded() {
        let deep = format!(
            "{}(space){}",
            "(group ".repeat(100_000),
            ")".repeat(100_000)
        );
        assert_eq!(parse(&deep, 1024), Err(ParseError::DepthExceeded(1024)));
    }

    #[test]
    fn script_operands_are_validated() {
        let empty = parse("(sub (slot 0) (space))", 8).unwrap();
        assert!(empty.script_operand_error().is_some());
        let nested = parse("(sup (slot 0) (sub (slot 1) (slot 2)))", 8).unwrap();
        assert!(nested.script_operand_error().is_some());
        let grouped = parse("(sup (slot 0) (group (sub (slot 1) (slot 2))))", 8).unwrap();
        assert!(grouped.script_operand_error().is_none());
        let frac = parse("(frac (seq (space)) (slot 0))", 8).unwrap();
        assert!(frac.script_operand_error().is_some());
    }

    #[test]
    fn walk_is_iterative_over_deep_trees() {
        let mut render = Render::Space;
        for _ in 0..200_000 {
            render = Render::Seq(vec![render, Render::Slot(0)]);
        }
        assert_eq!(render.slots().len(), 200_000);
        // Drop without recursion.
        let mut stack = vec![render];
        while let Some(node) = stack.pop() {
            match node {
                Render::Seq(items) => stack.extend(items),
                Render::Group(inner) | Render::Paren(inner) | Render::Bracket(inner) => {
                    stack.push(*inner);
                }
                Render::Sub(a, b) | Render::Sup(a, b) | Render::Frac(a, b) => {
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
    }
}
