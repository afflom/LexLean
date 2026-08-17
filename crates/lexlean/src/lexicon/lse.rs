//! LexLean Semantic Expressions (SPEC.md §13.8).
//!
//! The S-expression interface language for entry signatures and defined
//! values. Comments and quoted strings do not exist; whitespace is ASCII
//! space or LF only.
//!
//! Every parser here is depth-bounded and every walker over a parsed value
//! is iterative or bounded by the parsed depth. The bound is the project's
//! configured `max_scope_depth` (§25.5): a package expression may nest no
//! deeper than a source module may nest scopes, so one configured limit
//! covers both without a second, arbitrary constant. Exceeding it is an
//! explicit limit failure (`LLS8002`), never a stack abort.

use std::collections::{BTreeMap, BTreeSet};

/// A parsed qualified entry ID, `package::local-entry`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct QualifiedId {
    /// The package ID.
    pub package: String,
    /// The local entry ID.
    pub entry: String,
}

impl QualifiedId {
    /// Parse and validate `package::entry`.
    pub fn parse(text: &str) -> Result<Self, String> {
        let (package, entry) = text
            .split_once("::")
            .ok_or_else(|| format!("`{text}` is not a qualified `package::entry` ID"))?;
        if !is_package_id(package) {
            return Err(format!("`{package}` is not a valid package ID"));
        }
        if !is_entry_id(entry) {
            return Err(format!("`{entry}` is not a valid local entry ID"));
        }
        Ok(Self {
            package: package.to_owned(),
            entry: entry.to_owned(),
        })
    }
}

impl std::fmt::Display for QualifiedId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}::{}", self.package, self.entry)
    }
}

/// `[a-z][a-z0-9]*(\.[a-z][a-z0-9-]*)*` (SPEC.md §10.1).
#[must_use]
pub fn is_package_id(text: &str) -> bool {
    let mut segments = text.split('.');
    let Some(first) = segments.next() else {
        return false;
    };
    if !segment_matches(first, false) {
        return false;
    }
    segments.all(|segment| segment_matches(segment, true))
}

/// `[a-z][a-z0-9-]*(\.[a-z][a-z0-9-]*)*` (SPEC.md §13.1).
#[must_use]
pub fn is_entry_id(text: &str) -> bool {
    !text.is_empty()
        && text
            .split('.')
            .all(|segment| segment_matches(segment, true))
}

fn segment_matches(segment: &str, allow_hyphen: bool) -> bool {
    let bytes = segment.as_bytes();
    match bytes.first() {
        Some(b) if b.is_ascii_lowercase() => {}
        _ => return false,
    }
    bytes[1..]
        .iter()
        .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || (allow_hyphen && *b == b'-'))
}

/// An LSE local or universe identifier: ASCII letter then letters or digits.
#[must_use]
pub fn is_lse_identifier(text: &str) -> bool {
    let bytes = text.as_bytes();
    matches!(bytes.first(), Some(b) if b.is_ascii_alphabetic())
        && bytes[1..].iter().all(u8::is_ascii_alphanumeric)
}

/// A universe expression.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Universe {
    /// A decimal literal level.
    Num(u64),
    /// A declared universe variable.
    Var(String),
    /// `(succ u)`.
    Succ(Box<Universe>),
    /// `(max u v ...)`.
    Max(Vec<Universe>),
    /// `(imax u v)`.
    IMax(Box<Universe>, Box<Universe>),
}

/// A binder mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinderMode {
    /// `(explicit ...)`.
    Explicit,
    /// `(implicit ...)`.
    Implicit,
    /// `(instance ...)`.
    Instance,
}

impl BinderMode {
    /// The LSE keyword.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Explicit => "explicit",
            Self::Implicit => "implicit",
            Self::Instance => "instance",
        }
    }
}

/// One LSE binder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LseBinder {
    /// The mode.
    pub mode: BinderMode,
    /// The display name; identity is positional after parsing.
    pub name: String,
    /// The binder type.
    pub ty: Lse,
}

/// An LSE expression (SPEC.md §13.8).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lse {
    /// `(sort prop)`.
    SortProp,
    /// `(sort (type u))`.
    SortType(Universe),
    /// `(const qualified-id [universe-args])`.
    Const(QualifiedId, Vec<Universe>),
    /// `(local id)`.
    Local(String),
    /// `(app f a ...)`, at least one argument.
    App(Box<Lse>, Vec<Lse>),
    /// `(pi (binders...) body)`, at least one binder.
    Pi(Vec<LseBinder>, Box<Lse>),
    /// `(lam (binders...) body)`, at least one binder.
    Lam(Vec<LseBinder>, Box<Lse>),
    /// `(let id type value body)`.
    Let {
        /// The bound name.
        name: String,
        /// Its type.
        ty: Box<Lse>,
        /// Its value.
        value: Box<Lse>,
        /// The body.
        body: Box<Lse>,
    },
    /// `(nat decimal)`.
    Nat(String),
}

/// One token of the shared S-expression surface.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SexprToken {
    /// `(`.
    Open,
    /// `)`.
    Close,
    /// A bare atom.
    Atom(String),
}

/// Why an S-expression failed to parse: malformed text, or nesting beyond
/// the configured depth (§25.5). The two map to different diagnostics
/// (`LLR3004` and `LLS8002`), so the distinction is kept structurally.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError {
    /// Malformed expression text.
    Syntax(String),
    /// Nesting exceeded the configured `max_scope_depth`.
    DepthExceeded(u64),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Syntax(message) => f.write_str(message),
            Self::DepthExceeded(limit) => {
                write!(f, "max_scope_depth exceeded: configured {limit}")
            }
        }
    }
}

impl From<String> for ParseError {
    fn from(message: String) -> Self {
        Self::Syntax(message)
    }
}

/// Tokenize an S-expression: parens plus atoms, separated by one or more
/// ASCII spaces or LF; nothing else is whitespace and nothing is quoted. A
/// tab, CR, or other ASCII control scalar is rejected explicitly; any other
/// scalar becomes atom material and fails the atom grammar downstream.
pub fn sexpr_tokens(text: &str) -> Result<Vec<SexprToken>, String> {
    let mut tokens = Vec::new();
    let mut atom = String::new();
    for scalar in text.chars() {
        match scalar {
            '(' | ')' => {
                if !atom.is_empty() {
                    tokens.push(SexprToken::Atom(std::mem::take(&mut atom)));
                }
                tokens.push(if scalar == '(' {
                    SexprToken::Open
                } else {
                    SexprToken::Close
                });
            }
            ' ' | '\n' => {
                if !atom.is_empty() {
                    tokens.push(SexprToken::Atom(std::mem::take(&mut atom)));
                }
            }
            c if c.is_ascii_control() => {
                return Err("whitespace is one or more ASCII spaces or LF".to_owned());
            }
            c => atom.push(c),
        }
    }
    if !atom.is_empty() {
        tokens.push(SexprToken::Atom(atom));
    }
    Ok(tokens)
}

/// One node of the generic S-expression tree shared by the LSE and LRE
/// parsers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Node {
    /// A bare atom.
    Atom(String),
    /// A parenthesized list, possibly empty.
    List(Vec<Node>),
}

impl Node {
    pub(crate) fn describe(&self) -> String {
        match self {
            Node::Atom(text) => format!("`{text}`"),
            Node::List(items) => match items.first() {
                Some(Node::Atom(head)) => format!("`({head} ...)`"),
                _ => "a list".to_owned(),
            },
        }
    }
}

/// Read one complete S-expression into a generic tree, iteratively, with
/// list nesting bounded by `max_depth` (the configured `max_scope_depth`).
pub(crate) fn read_tree(text: &str, max_depth: u64) -> Result<Node, ParseError> {
    let tokens = sexpr_tokens(text)?;
    let mut stack: Vec<Vec<Node>> = Vec::new();
    let mut root: Option<Node> = None;
    for token in tokens {
        if root.is_some() {
            return Err(ParseError::Syntax(
                "trailing tokens after the expression".to_owned(),
            ));
        }
        match token {
            SexprToken::Open => {
                if stack.len() as u64 >= max_depth {
                    return Err(ParseError::DepthExceeded(max_depth));
                }
                stack.push(Vec::new());
            }
            SexprToken::Close => {
                let Some(items) = stack.pop() else {
                    return Err(ParseError::Syntax("unbalanced `)`".to_owned()));
                };
                let node = Node::List(items);
                match stack.last_mut() {
                    Some(parent) => parent.push(node),
                    None => root = Some(node),
                }
            }
            SexprToken::Atom(text) => match stack.last_mut() {
                Some(parent) => parent.push(Node::Atom(text)),
                None => root = Some(Node::Atom(text)),
            },
        }
    }
    if !stack.is_empty() {
        return Err(ParseError::Syntax(
            "unexpected end of expression".to_owned(),
        ));
    }
    root.ok_or_else(|| ParseError::Syntax("unexpected end of expression".to_owned()))
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

/// Convert a universe node, iteratively.
fn universe_of(node: &Node) -> Result<Universe, ParseError> {
    enum Work<'a> {
        Visit(&'a Node),
        Build(&'a str, usize),
    }
    let mut work = vec![Work::Visit(node)];
    let mut values: Vec<Universe> = Vec::new();
    while let Some(item) = work.pop() {
        match item {
            Work::Visit(Node::Atom(text)) => {
                if text.bytes().all(|b| b.is_ascii_digit()) {
                    values.push(Universe::Num(parse_decimal(text)?));
                } else if is_lse_identifier(text) {
                    values.push(Universe::Var(text.clone()));
                } else {
                    return Err(syntax(format!("`{text}` is not a universe")));
                }
            }
            Work::Visit(Node::List(items)) => {
                let Some(Node::Atom(head)) = items.first() else {
                    return Err(syntax("expected a universe form"));
                };
                let arguments = &items[1..];
                match head.as_str() {
                    "succ" if arguments.len() == 1 => {}
                    "max" if arguments.len() >= 2 => {}
                    "imax" if arguments.len() == 2 => {}
                    "succ" | "max" | "imax" => {
                        return Err(syntax(format!("`({head} ...)` has the wrong arity")))
                    }
                    other => return Err(syntax(format!("`{other}` is not a universe form"))),
                }
                work.push(Work::Build(head, arguments.len()));
                for argument in arguments.iter().rev() {
                    work.push(Work::Visit(argument));
                }
            }
            Work::Build(head, count) => {
                let start = values.len().saturating_sub(count);
                let arguments: Vec<Universe> = values.drain(start..).collect();
                let mut arguments = arguments.into_iter();
                let built = match head {
                    "succ" => Universe::Succ(Box::new(
                        arguments.next().ok_or_else(|| syntax("missing operand"))?,
                    )),
                    "imax" => {
                        let a = arguments.next().ok_or_else(|| syntax("missing operand"))?;
                        let b = arguments.next().ok_or_else(|| syntax("missing operand"))?;
                        Universe::IMax(Box::new(a), Box::new(b))
                    }
                    _ => Universe::Max(arguments.collect()),
                };
                values.push(built);
            }
        }
    }
    values.pop().ok_or_else(|| syntax("expected a universe"))
}

fn binder_header(node: &Node) -> Result<(BinderMode, String, &Node), ParseError> {
    let Node::List(items) = node else {
        return Err(syntax(format!(
            "expected a binder, found {}",
            node.describe()
        )));
    };
    if items.len() != 3 {
        return Err(syntax("a binder is `(mode name type)`"));
    }
    let mode = match atom_of(&items[0], "a binder mode")?.as_str() {
        "explicit" => BinderMode::Explicit,
        "implicit" => BinderMode::Implicit,
        "instance" => BinderMode::Instance,
        other => return Err(syntax(format!("`{other}` is not a binder mode"))),
    };
    let name = atom_of(&items[1], "a local ID")?;
    if !is_lse_identifier(&name) {
        return Err(syntax(format!("`{name}` is not a valid local ID")));
    }
    Ok((mode, name, &items[2]))
}

/// Convert a generic tree into an LSE expression, iteratively: a work stack
/// visits sub-expressions in order and builds each form once its children
/// are on the value stack.
fn lse_of(root: &Node) -> Result<Lse, ParseError> {
    enum Work<'a> {
        Visit(&'a Node),
        Build(&'a Node),
    }
    let mut work = vec![Work::Visit(root)];
    let mut values: Vec<Lse> = Vec::new();
    while let Some(item) = work.pop() {
        match item {
            Work::Visit(node) => {
                let Node::List(items) = node else {
                    return Err(syntax(format!("expected `(`, found {}", node.describe())));
                };
                let Some(Node::Atom(head)) = items.first() else {
                    return Err(syntax("expected an LSE form"));
                };
                let arguments = &items[1..];
                match head.as_str() {
                    "sort" | "const" | "local" | "nat" => {
                        // Leaves: built directly.
                        values.push(leaf_of(head, arguments)?);
                    }
                    "app" => {
                        if arguments.len() < 2 {
                            return Err(syntax("`app` has at least a function and one argument"));
                        }
                        work.push(Work::Build(node));
                        for argument in arguments.iter().rev() {
                            work.push(Work::Visit(argument));
                        }
                    }
                    "pi" | "lam" => {
                        if arguments.len() != 2 {
                            return Err(syntax(format!(
                                "`{head}` is `({head} (binders...) body)`"
                            )));
                        }
                        let Node::List(binders) = &arguments[0] else {
                            return Err(syntax("expected a binder list"));
                        };
                        if binders.is_empty() {
                            return Err(syntax(format!("`{head}` has at least one binder")));
                        }
                        work.push(Work::Build(node));
                        work.push(Work::Visit(&arguments[1]));
                        for binder in binders.iter().rev() {
                            let (_, _, ty) = binder_header(binder)?;
                            work.push(Work::Visit(ty));
                        }
                    }
                    "let" => {
                        if arguments.len() != 4 {
                            return Err(syntax("`let` is `(let name type value body)`"));
                        }
                        let name = atom_of(&arguments[0], "a local ID")?;
                        if !is_lse_identifier(&name) {
                            return Err(syntax(format!("`{name}` is not a valid local ID")));
                        }
                        work.push(Work::Build(node));
                        for argument in arguments[1..].iter().rev() {
                            work.push(Work::Visit(argument));
                        }
                    }
                    other => return Err(syntax(format!("`{other}` is not an LSE form"))),
                }
            }
            Work::Build(node) => {
                let Node::List(items) = node else {
                    return Err(syntax("expected a list"));
                };
                let head = atom_of(&items[0], "a form")?;
                let arguments = &items[1..];
                let built = match head.as_str() {
                    "app" => {
                        let start = values.len().saturating_sub(arguments.len());
                        let mut parts = values.drain(start..);
                        let function = parts.next().ok_or_else(|| syntax("missing function"))?;
                        Lse::App(Box::new(function), parts.collect())
                    }
                    "pi" | "lam" => {
                        let Node::List(binder_nodes) = &arguments[0] else {
                            return Err(syntax("expected a binder list"));
                        };
                        let count = binder_nodes.len().saturating_add(1);
                        let start = values.len().saturating_sub(count);
                        let mut parts: Vec<Lse> = values.drain(start..).collect();
                        let body = parts.pop().ok_or_else(|| syntax("missing body"))?;
                        let mut binders = Vec::new();
                        for (binder_node, ty) in binder_nodes.iter().zip(parts) {
                            let (mode, name, _) = binder_header(binder_node)?;
                            binders.push(LseBinder { mode, name, ty });
                        }
                        if head == "pi" {
                            Lse::Pi(binders, Box::new(body))
                        } else {
                            Lse::Lam(binders, Box::new(body))
                        }
                    }
                    _ => {
                        let start = values.len().saturating_sub(3);
                        let mut parts = values.drain(start..);
                        let ty = parts.next().ok_or_else(|| syntax("missing type"))?;
                        let value = parts.next().ok_or_else(|| syntax("missing value"))?;
                        let body = parts.next().ok_or_else(|| syntax("missing body"))?;
                        Lse::Let {
                            name: atom_of(&arguments[0], "a local ID")?,
                            ty: Box::new(ty),
                            value: Box::new(value),
                            body: Box::new(body),
                        }
                    }
                };
                values.push(built);
            }
        }
    }
    match (values.pop(), values.is_empty()) {
        (Some(expr), true) => Ok(expr),
        _ => Err(syntax("malformed expression")),
    }
}

fn leaf_of(head: &str, arguments: &[Node]) -> Result<Lse, ParseError> {
    match head {
        "sort" => match arguments {
            [Node::Atom(text)] if text == "prop" => Ok(Lse::SortProp),
            [Node::List(inner)] => match inner.as_slice() {
                [Node::Atom(keyword), universe] if keyword == "type" => {
                    Ok(Lse::SortType(universe_of(universe)?))
                }
                _ => Err(syntax("a sort is `(sort prop)` or `(sort (type u))`")),
            },
            _ => Err(syntax("a sort is `(sort prop)` or `(sort (type u))`")),
        },
        "const" => match arguments {
            [Node::Atom(id)] => Ok(Lse::Const(QualifiedId::parse(id)?, Vec::new())),
            [Node::Atom(id), Node::List(universes)] if !universes.is_empty() => Ok(Lse::Const(
                QualifiedId::parse(id)?,
                universes
                    .iter()
                    .map(universe_of)
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            _ => Err(syntax("a const is `(const qualified-id [universes])`")),
        },
        "local" => match arguments {
            [Node::Atom(name)] if is_lse_identifier(name) => Ok(Lse::Local(name.clone())),
            [Node::Atom(name)] => Err(syntax(format!("`{name}` is not a valid local ID"))),
            _ => Err(syntax("a local is `(local id)`")),
        },
        "nat" => match arguments {
            [Node::Atom(digits)] => {
                parse_decimal(digits)?;
                Ok(Lse::Nat(digits.clone()))
            }
            _ => Err(syntax("a nat is `(nat decimal)`")),
        },
        other => Err(syntax(format!("`{other}` is not an LSE form"))),
    }
}

/// Parse a canonical decimal: digits only, no redundant leading zero, and
/// within 64 bits.
pub fn parse_decimal(text: &str) -> Result<u64, String> {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("`{text}` is not a decimal"));
    }
    if text.len() > 1 && text.starts_with('0') {
        return Err(format!("`{text}` has a redundant leading zero"));
    }
    text.parse::<u64>()
        .map_err(|_| format!("`{text}` does not fit 64 bits"))
}

/// Parse one complete LSE expression, nesting bounded by `max_depth` (the
/// configured `max_scope_depth`). Both the reader and the conversion are
/// iterative, so no input depth can exhaust the stack.
pub fn parse(text: &str, max_depth: u64) -> Result<Lse, ParseError> {
    let tree = read_tree(text, max_depth)?;
    lse_of(&tree)
}

fn universe_text(u: &Universe, out: &mut String) {
    // Universe nesting is bounded by the parser's depth counter, so this
    // small recursion is bounded by the configured limit.
    match u {
        Universe::Num(n) => out.push_str(&n.to_string()),
        Universe::Var(name) => out.push_str(name),
        Universe::Succ(inner) => {
            out.push_str("(succ ");
            universe_text(inner, out);
            out.push(')');
        }
        Universe::Max(items) => {
            out.push_str("(max");
            for item in items {
                out.push(' ');
                universe_text(item, out);
            }
            out.push(')');
        }
        Universe::IMax(a, b) => {
            out.push_str("(imax ");
            universe_text(a, out);
            out.push(' ');
            universe_text(b, out);
            out.push(')');
        }
    }
}

fn check_universe(u: &Universe, declared: &BTreeSet<String>) -> Result<(), String> {
    match u {
        Universe::Num(_) => Ok(()),
        Universe::Var(name) => {
            if declared.contains(name) {
                Ok(())
            } else {
                Err(format!("universe variable `{name}` is not declared"))
            }
        }
        Universe::Succ(inner) => check_universe(inner, declared),
        Universe::Max(items) => items.iter().try_for_each(|i| check_universe(i, declared)),
        Universe::IMax(a, b) => {
            check_universe(a, declared)?;
            check_universe(b, declared)
        }
    }
}

impl Lse {
    /// Check scoping: every `(local x)` resolves lexically and every
    /// universe variable is declared (§13.8). Iterative: the traversal
    /// depth never depends on the expression depth.
    pub fn check_scopes(&self, universes: &BTreeSet<String>) -> Result<(), String> {
        enum Item<'a> {
            Expr(&'a Lse),
            Bind(&'a str),
            Truncate(usize),
        }
        let mut scope: Vec<&str> = Vec::new();
        let mut stack: Vec<Item<'_>> = vec![Item::Expr(self)];
        while let Some(item) = stack.pop() {
            match item {
                Item::Bind(name) => scope.push(name),
                Item::Truncate(depth) => scope.truncate(depth),
                Item::Expr(expr) => match expr {
                    Lse::SortProp | Lse::Nat(_) => {}
                    Lse::SortType(u) => check_universe(u, universes)?,
                    Lse::Const(_, args) => {
                        args.iter().try_for_each(|u| check_universe(u, universes))?;
                    }
                    Lse::Local(name) => {
                        if !scope.iter().any(|s| s == name) {
                            return Err(format!("local `{name}` is not in scope"));
                        }
                    }
                    Lse::App(function, arguments) => {
                        for argument in arguments.iter().rev() {
                            stack.push(Item::Expr(argument));
                        }
                        stack.push(Item::Expr(function));
                    }
                    Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
                        stack.push(Item::Truncate(scope.len()));
                        stack.push(Item::Expr(body));
                        for binder in binders.iter().rev() {
                            stack.push(Item::Bind(&binder.name));
                            stack.push(Item::Expr(&binder.ty));
                        }
                    }
                    Lse::Let {
                        name,
                        ty,
                        value,
                        body,
                    } => {
                        stack.push(Item::Truncate(scope.len()));
                        stack.push(Item::Expr(body));
                        stack.push(Item::Bind(name));
                        stack.push(Item::Expr(value));
                        stack.push(Item::Expr(ty));
                    }
                },
            }
        }
        Ok(())
    }

    /// Canonical printing (§13.8): one ASCII space between atoms, no
    /// redundant grouping. With `alpha_rename`, binders become `x0`, `x1`,
    /// ... in binding order, the form hashed for signature identity.
    /// Iterative over an explicit work stack.
    #[must_use]
    pub fn print(&self, alpha_rename: bool) -> String {
        enum Item<'a> {
            Expr(&'a Lse),
            Text(&'static str),
            Binder(&'a LseBinder),
            LetHead(&'a str),
            Bind(&'a str, String),
            Truncate(usize),
        }
        let mut out = String::new();
        let mut scope: Vec<(&str, String)> = Vec::new();
        let mut counter: usize = 0;
        let fresh = |name: &str, counter: &mut usize| -> String {
            if alpha_rename {
                let shown = format!("x{counter}");
                *counter = counter.saturating_add(1);
                shown
            } else {
                name.to_owned()
            }
        };
        let mut stack: Vec<Item<'_>> = vec![Item::Expr(self)];
        while let Some(item) = stack.pop() {
            match item {
                Item::Text(text) => out.push_str(text),
                Item::Bind(name, shown) => scope.push((name, shown)),
                Item::Truncate(depth) => scope.truncate(depth),
                Item::Binder(binder) => {
                    let shown = fresh(&binder.name, &mut counter);
                    out.push('(');
                    out.push_str(binder.mode.as_str());
                    out.push(' ');
                    out.push_str(&shown);
                    out.push(' ');
                    stack.push(Item::Bind(&binder.name, shown));
                    stack.push(Item::Text(")"));
                    stack.push(Item::Expr(&binder.ty));
                }
                Item::LetHead(name) => {
                    let shown = fresh(name, &mut counter);
                    out.push_str(&shown);
                    out.push(' ');
                    stack.push(Item::Bind(name, shown));
                }
                Item::Expr(expr) => match expr {
                    Lse::SortProp => out.push_str("(sort prop)"),
                    Lse::SortType(u) => {
                        out.push_str("(sort (type ");
                        universe_text(u, &mut out);
                        out.push_str("))");
                    }
                    Lse::Const(id, args) => {
                        out.push_str("(const ");
                        out.push_str(&id.to_string());
                        if !args.is_empty() {
                            out.push_str(" (");
                            for (index, arg) in args.iter().enumerate() {
                                if index > 0 {
                                    out.push(' ');
                                }
                                universe_text(arg, &mut out);
                            }
                            out.push(')');
                        }
                        out.push(')');
                    }
                    Lse::Local(name) => {
                        out.push_str("(local ");
                        let shown = if alpha_rename {
                            scope
                                .iter()
                                .rev()
                                .find(|(original, _)| *original == name)
                                .map_or_else(|| name.clone(), |(_, renamed)| renamed.clone())
                        } else {
                            name.clone()
                        };
                        out.push_str(&shown);
                        out.push(')');
                    }
                    Lse::App(function, arguments) => {
                        out.push_str("(app ");
                        stack.push(Item::Text(")"));
                        for argument in arguments.iter().rev() {
                            stack.push(Item::Expr(argument));
                            stack.push(Item::Text(" "));
                        }
                        stack.push(Item::Expr(function));
                    }
                    Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
                        out.push_str(if matches!(expr, Lse::Pi(..)) {
                            "(pi ("
                        } else {
                            "(lam ("
                        });
                        stack.push(Item::Truncate(scope.len()));
                        stack.push(Item::Text(")"));
                        stack.push(Item::Expr(body));
                        stack.push(Item::Text(") "));
                        for (index, binder) in binders.iter().enumerate().rev() {
                            stack.push(Item::Binder(binder));
                            if index > 0 {
                                stack.push(Item::Text(" "));
                            }
                        }
                    }
                    Lse::Let {
                        name,
                        ty,
                        value,
                        body,
                    } => {
                        out.push_str("(let ");
                        stack.push(Item::Truncate(scope.len()));
                        stack.push(Item::Text(")"));
                        stack.push(Item::Expr(body));
                        stack.push(Item::Text(" "));
                        stack.push(Item::Expr(value));
                        stack.push(Item::Text(" "));
                        stack.push(Item::Expr(ty));
                        stack.push(Item::LetHead(name));
                    }
                    Lse::Nat(digits) => {
                        out.push_str("(nat ");
                        out.push_str(digits);
                        out.push(')');
                    }
                },
            }
        }
        out
    }

    /// Every qualified constant referenced by this expression, in
    /// occurrence order. Iterative.
    #[must_use]
    pub fn referenced_consts(&self) -> Vec<QualifiedId> {
        let mut out = Vec::new();
        let mut stack: Vec<&Lse> = vec![self];
        while let Some(expr) = stack.pop() {
            match expr {
                Lse::Const(id, _) => out.push(id.clone()),
                Lse::App(function, arguments) => {
                    for argument in arguments.iter().rev() {
                        stack.push(argument);
                    }
                    stack.push(function);
                }
                Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
                    stack.push(body);
                    for binder in binders.iter().rev() {
                        stack.push(&binder.ty);
                    }
                }
                Lse::Let {
                    ty, value, body, ..
                } => {
                    stack.push(body);
                    stack.push(value);
                    stack.push(ty);
                }
                Lse::SortProp | Lse::SortType(_) | Lse::Local(_) | Lse::Nat(_) => {}
            }
        }
        out
    }

    /// The number of explicit binders of the outermost `pi`, or 0 when the
    /// expression is not a `pi`. This is the surface arity a signature
    /// fixes for its entry (§13.4, §13.9: every explicit surface argument is
    /// one slot).
    #[must_use]
    pub fn outer_explicit_binders(&self) -> usize {
        match self {
            Lse::Pi(binders, _) => binders
                .iter()
                .filter(|binder| binder.mode == BinderMode::Explicit)
                .count(),
            _ => 0,
        }
    }

    /// The outermost `pi`'s result after all its binders, or the expression
    /// itself for a non-`pi`.
    #[must_use]
    pub fn result(&self) -> &Lse {
        match self {
            Lse::Pi(_, body) => body,
            other => other,
        }
    }
}

// ---------------------------------------------------------------------------
// The conservative LSE checker (§13.7, §13.8, §14.4).
// ---------------------------------------------------------------------------

/// What the checker knows about a referenced constant.
#[derive(Debug, Clone, Copy)]
pub enum ConstInfo<'a> {
    /// The constant does not resolve.
    Missing,
    /// The constant lives in another package that is not consulted in this
    /// check (the package-local check at load): its type is unknown and it
    /// may unfold to any shape, so nothing rigid is concluded from it.
    Opaque,
    /// The constant resolves to an entry without a signature (structural,
    /// grammar, or label-word).
    NoSignature,
    /// The constant's signature; `defined` says the entry has a defined
    /// denotation, which may unfold to another type shape and therefore
    /// blocks rigid mismatch conclusions.
    Signature {
        /// The signature.
        signature: &'a Lse,
        /// Whether the entry is a defined lexicon value.
        defined: bool,
    },
}

/// A checker failure: the message names the offending sub-expression in
/// canonical print.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeError {
    /// The specific message.
    pub message: String,
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

/// The result of checking one expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Checked {
    /// The inferred type (may contain unresolved implicit arguments printed
    /// as `?n` locals).
    pub ty: Lse,
    /// For every `(nat ...)` literal in pre-order occurrence, its inferred
    /// type when the expected type was determined by an explicit binder of a
    /// known function (or by the signature the value must match), otherwise
    /// `None`.
    pub literal_types: Vec<Option<Lse>>,
}

/// Is `name` a checker metavariable? Metavariables use `?` prefixes, which
/// the LSE identifier grammar never admits, so they cannot collide with a
/// user local.
fn is_meta(name: &str) -> bool {
    name.starts_with('?')
}

type Lookup<'a> = &'a dyn Fn(&QualifiedId) -> ConstInfo<'a>;

struct Checker<'a> {
    lookup: Lookup<'a>,
    metas: BTreeMap<String, Option<Lse>>,
    next_meta: usize,
    literal_metas: Vec<String>,
    /// Counter for capture-avoiding renames.
    fresh_counter: usize,
}

fn free_locals(expr: &Lse, out: &mut BTreeSet<String>) {
    let mut stack: Vec<(&Lse, Vec<&str>)> = vec![(expr, Vec::new())];
    while let Some((expr, bound)) = stack.pop() {
        match expr {
            Lse::Local(name) => {
                if !bound.iter().any(|b| b == name) {
                    out.insert(name.clone());
                }
            }
            Lse::App(function, arguments) => {
                for argument in arguments {
                    stack.push((argument, bound.clone()));
                }
                stack.push((function, bound));
            }
            Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
                let mut inner = bound.clone();
                for binder in binders {
                    stack.push((&binder.ty, inner.clone()));
                    inner.push(&binder.name);
                }
                stack.push((body, inner));
            }
            Lse::Let {
                name,
                ty,
                value,
                body,
            } => {
                stack.push((ty, bound.clone()));
                stack.push((value, bound.clone()));
                let mut inner = bound;
                inner.push(name);
                stack.push((body, inner));
            }
            Lse::SortProp | Lse::SortType(_) | Lse::Const(..) | Lse::Nat(_) => {}
        }
    }
}

impl<'a> Checker<'a> {
    fn new(lookup: Lookup<'a>) -> Self {
        Self {
            lookup,
            metas: BTreeMap::new(),
            next_meta: 0,
            literal_metas: Vec::new(),
            fresh_counter: 0,
        }
    }

    fn fresh_meta(&mut self) -> Lse {
        let name = format!("?{}", self.next_meta);
        self.next_meta = self.next_meta.saturating_add(1);
        self.metas.insert(name.clone(), None);
        Lse::Local(name)
    }

    fn fresh_local(&mut self, base: &str) -> String {
        self.fresh_counter = self.fresh_counter.saturating_add(1);
        format!("{base}#{}", self.fresh_counter)
    }

    /// Replace bound metavariables by their solutions, recursively. The
    /// recursion depth is the parsed expression depth.
    fn zonk(&self, expr: &Lse) -> Lse {
        match expr {
            Lse::Local(name) if is_meta(name) => match self.metas.get(name) {
                Some(Some(solution)) => self.zonk(solution),
                _ => expr.clone(),
            },
            Lse::App(function, arguments) => Lse::App(
                Box::new(self.zonk(function)),
                arguments.iter().map(|a| self.zonk(a)).collect(),
            ),
            Lse::Pi(binders, body) => Lse::Pi(
                binders
                    .iter()
                    .map(|b| LseBinder {
                        mode: b.mode,
                        name: b.name.clone(),
                        ty: self.zonk(&b.ty),
                    })
                    .collect(),
                Box::new(self.zonk(body)),
            ),
            Lse::Lam(binders, body) => Lse::Lam(
                binders
                    .iter()
                    .map(|b| LseBinder {
                        mode: b.mode,
                        name: b.name.clone(),
                        ty: self.zonk(&b.ty),
                    })
                    .collect(),
                Box::new(self.zonk(body)),
            ),
            Lse::Let {
                name,
                ty,
                value,
                body,
            } => Lse::Let {
                name: name.clone(),
                ty: Box::new(self.zonk(ty)),
                value: Box::new(self.zonk(value)),
                body: Box::new(self.zonk(body)),
            },
            other => other.clone(),
        }
    }

    fn has_unsolved_meta(&self, expr: &Lse) -> bool {
        let zonked = self.zonk(expr);
        let mut free = BTreeSet::new();
        free_locals(&zonked, &mut free);
        free.iter().any(|name| is_meta(name))
    }

    /// Capture-avoiding substitution of `name` by `replacement`.
    fn subst(&mut self, expr: &Lse, name: &str, replacement: &Lse) -> Lse {
        let mut avoid = BTreeSet::new();
        free_locals(replacement, &mut avoid);
        self.subst_in(expr, name, replacement, &avoid)
    }

    fn subst_binders(
        &mut self,
        binders: &[LseBinder],
        body: &Lse,
        name: &str,
        replacement: &Lse,
        avoid: &BTreeSet<String>,
    ) -> (Vec<LseBinder>, Lse) {
        let mut out = Vec::new();
        // Renamings introduced for capture avoidance, applied to later
        // binder types and the body.
        let mut renames: Vec<(String, String)> = Vec::new();
        let mut shadowed = false;
        for binder in binders {
            let mut ty = binder.ty.clone();
            for (from, to) in &renames {
                ty = self.subst_in(&ty, from, &Lse::Local(to.clone()), &BTreeSet::new());
            }
            if !shadowed {
                ty = self.subst_in(&ty, name, replacement, avoid);
            }
            let mut shown = binder.name.clone();
            if binder.name == name {
                shadowed = true;
            } else if avoid.contains(&binder.name) {
                shown = self.fresh_local(&binder.name);
                renames.push((binder.name.clone(), shown.clone()));
            }
            out.push(LseBinder {
                mode: binder.mode,
                name: shown,
                ty,
            });
        }
        let mut new_body = body.clone();
        for (from, to) in &renames {
            new_body = self.subst_in(&new_body, from, &Lse::Local(to.clone()), &BTreeSet::new());
        }
        if !shadowed {
            new_body = self.subst_in(&new_body, name, replacement, avoid);
        }
        (out, new_body)
    }

    fn subst_in(
        &mut self,
        expr: &Lse,
        name: &str,
        replacement: &Lse,
        avoid: &BTreeSet<String>,
    ) -> Lse {
        match expr {
            Lse::Local(local) if local == name => replacement.clone(),
            Lse::App(function, arguments) => Lse::App(
                Box::new(self.subst_in(function, name, replacement, avoid)),
                arguments
                    .iter()
                    .map(|a| self.subst_in(a, name, replacement, avoid))
                    .collect(),
            ),
            Lse::Pi(binders, body) => {
                let (binders, body) = self.subst_binders(binders, body, name, replacement, avoid);
                Lse::Pi(binders, Box::new(body))
            }
            Lse::Lam(binders, body) => {
                let (binders, body) = self.subst_binders(binders, body, name, replacement, avoid);
                Lse::Lam(binders, Box::new(body))
            }
            Lse::Let {
                name: bound,
                ty,
                value,
                body,
            } => {
                let ty = self.subst_in(ty, name, replacement, avoid);
                let value = self.subst_in(value, name, replacement, avoid);
                if bound == name {
                    Lse::Let {
                        name: bound.clone(),
                        ty: Box::new(ty),
                        value: Box::new(value),
                        body: body.clone(),
                    }
                } else if avoid.contains(bound) {
                    let shown = self.fresh_local(bound);
                    let renamed =
                        self.subst_in(body, bound, &Lse::Local(shown.clone()), &BTreeSet::new());
                    Lse::Let {
                        name: shown,
                        ty: Box::new(ty),
                        value: Box::new(value),
                        body: Box::new(self.subst_in(&renamed, name, replacement, avoid)),
                    }
                } else {
                    Lse::Let {
                        name: bound.clone(),
                        ty: Box::new(ty),
                        value: Box::new(value),
                        body: Box::new(self.subst_in(body, name, replacement, avoid)),
                    }
                }
            }
            other => other.clone(),
        }
    }

    /// May this expression unfold to another shape: a defined lexicon
    /// value, or a constant opaque to this check?
    fn may_unfold(&self, expr: &Lse) -> bool {
        match expr {
            Lse::Const(id, _) => matches!(
                (self.lookup)(id),
                ConstInfo::Signature { defined: true, .. } | ConstInfo::Opaque
            ),
            Lse::App(function, _) => self.may_unfold(function),
            _ => false,
        }
    }

    /// Conservative unification. `Ok(())` means compatible or undecidable;
    /// `Err` is a rigid mismatch that no instantiation can repair.
    fn unify(&mut self, expected: &Lse, actual: &Lse) -> Result<(), TypeError> {
        let expected = self.zonk(expected);
        let actual = self.zonk(actual);
        for (meta_side, other) in [(&expected, &actual), (&actual, &expected)] {
            if let Lse::Local(m) = meta_side {
                if is_meta(m) {
                    if let Lse::Local(n) = other {
                        if n == m {
                            return Ok(());
                        }
                    }
                    self.metas.insert(m.clone(), Some(other.clone()));
                    return Ok(());
                }
            }
        }
        match (&expected, &actual) {
            (Lse::SortProp, Lse::SortProp) | (Lse::SortType(_), Lse::SortType(_)) => Ok(()),
            (Lse::Const(x, _), Lse::Const(y, _)) if x == y => Ok(()),
            (Lse::Local(x), Lse::Local(y)) if x == y => Ok(()),
            (Lse::Nat(x), Lse::Nat(y)) if x == y => Ok(()),
            (Lse::App(f, xs), Lse::App(g, ys)) if xs.len() == ys.len() => {
                if self.may_unfold(&expected) || self.may_unfold(&actual) {
                    return Ok(());
                }
                self.unify(f, g)?;
                for (x, y) in xs.iter().zip(ys) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (Lse::Pi(..), Lse::Pi(..)) | (Lse::Lam(..), Lse::Lam(..)) => {
                let flat_e = flatten(&expected);
                let flat_a = flatten(&actual);
                if flat_e.0.len() != flat_a.0.len() {
                    return Err(TypeError {
                        message: format!(
                            "`{}` binds {} arguments but `{}` binds {}",
                            expected.print(false),
                            flat_e.0.len(),
                            actual.print(false),
                            flat_a.0.len()
                        ),
                    });
                }
                let mut body_a = flat_a.1.clone();
                let mut later_a: Vec<LseBinder> = flat_a.0.clone();
                for (index, (be, ba)) in flat_e.0.iter().zip(flat_a.0.iter()).enumerate() {
                    if be.mode != ba.mode {
                        return Err(TypeError {
                            message: format!(
                                "binder `{}` is {} in `{}` but `{}` is {} in `{}`",
                                be.name,
                                be.mode.as_str(),
                                expected.print(false),
                                ba.name,
                                ba.mode.as_str(),
                                actual.print(false)
                            ),
                        });
                    }
                    let ty_a = later_a
                        .get(index)
                        .map(|b| b.ty.clone())
                        .unwrap_or(Lse::SortProp);
                    self.unify(&be.ty, &ty_a)?;
                    // Identify the two binders for the remainder.
                    let renamed = Lse::Local(be.name.clone());
                    for later in later_a.iter_mut().skip(index.saturating_add(1)) {
                        later.ty = self.subst(&later.ty, &ba.name, &renamed);
                    }
                    body_a = self.subst(&body_a, &ba.name, &renamed);
                }
                self.unify(&flat_e.1, &body_a)
            }
            _ => {
                if self.may_unfold(&expected) || self.may_unfold(&actual) {
                    return Ok(());
                }
                if self.has_unsolved_meta(&expected) || self.has_unsolved_meta(&actual) {
                    return Ok(());
                }
                Err(TypeError {
                    message: format!(
                        "expected `{}`, found `{}`",
                        expected.print(false),
                        actual.print(false)
                    ),
                })
            }
        }
    }

    /// `expr` (whose inferred type is `ty`) must be a type: its type is a
    /// sort, or undecidable.
    fn require_sort(&self, expr: &Lse, ty: &Lse) -> Result<Lse, TypeError> {
        let ty = self.zonk(ty);
        if matches!(expr, Lse::Nat(_) | Lse::Lam(..)) {
            return Err(TypeError {
                message: format!("`{}` is a term, not a type", expr.print(false)),
            });
        }
        match &ty {
            Lse::SortProp | Lse::SortType(_) => Ok(ty),
            Lse::Local(m) if is_meta(m) => Ok(ty),
            _ if self.may_unfold(&ty) => Ok(ty),
            other => Err(TypeError {
                message: format!(
                    "`{}` is not a type: its type is `{}`",
                    expr.print(false),
                    other.print(false)
                ),
            }),
        }
    }

    fn expect_type(
        &mut self,
        expr: &Lse,
        scope: &mut Vec<(String, Lse)>,
    ) -> Result<Lse, TypeError> {
        let ty = self.infer(expr, scope)?;
        self.require_sort(expr, &ty)
    }

    #[allow(clippy::too_many_lines)]
    fn infer(&mut self, expr: &Lse, scope: &mut Vec<(String, Lse)>) -> Result<Lse, TypeError> {
        match expr {
            Lse::SortProp => Ok(Lse::SortType(Universe::Num(1))),
            Lse::SortType(u) => Ok(Lse::SortType(Universe::Succ(Box::new(u.clone())))),
            Lse::Const(id, _) => match (self.lookup)(id) {
                ConstInfo::Missing => Err(TypeError {
                    message: format!("`{id}` does not resolve"),
                }),
                ConstInfo::Opaque => Ok(self.fresh_meta()),
                ConstInfo::NoSignature => Err(TypeError {
                    message: format!("`{id}` has no signature and cannot appear in an expression"),
                }),
                ConstInfo::Signature { signature, .. } => Ok(signature.clone()),
            },
            Lse::Local(name) => {
                if is_meta(name) {
                    return Ok(self.fresh_meta());
                }
                scope
                    .iter()
                    .rev()
                    .find(|(local, _)| local == name)
                    .map(|(_, ty)| ty.clone())
                    .ok_or_else(|| TypeError {
                        message: format!("local `{name}` is not in scope"),
                    })
            }
            Lse::Nat(_) => {
                let meta = self.fresh_meta();
                if let Lse::Local(name) = &meta {
                    self.literal_metas.push(name.clone());
                }
                Ok(meta)
            }
            Lse::App(function, arguments) => {
                if matches!(**function, Lse::Nat(_) | Lse::SortProp | Lse::SortType(_)) {
                    return Err(TypeError {
                        message: format!(
                            "`{}` applies `{}`, which is not a function",
                            expr.print(false),
                            function.print(false)
                        ),
                    });
                }
                let mut fty = self.infer(function, scope)?;
                let mut remaining: &[Lse] = arguments;
                let mut supplied = 0usize;
                while !remaining.is_empty() {
                    let zonked = self.zonk(&fty);
                    let (binders, body) = match &zonked {
                        Lse::Pi(binders, body) => (binders.clone(), (**body).clone()),
                        Lse::Local(m) if is_meta(m) => {
                            // An unknown function type: consume the rest
                            // without judgement, still visiting literals.
                            for argument in remaining {
                                self.infer(argument, scope)?;
                            }
                            return Ok(self.fresh_meta());
                        }
                        other if self.may_unfold(other) => {
                            for argument in remaining {
                                self.infer(argument, scope)?;
                            }
                            return Ok(self.fresh_meta());
                        }
                        other => {
                            return Err(TypeError {
                                message: format!(
                                    "`{}` supplies {} explicit argument{} but `{}` accepts {supplied}: after them its type is `{}`, not a function",
                                    expr.print(false),
                                    arguments.len(),
                                    if arguments.len() == 1 { "" } else { "s" },
                                    function.print(false),
                                    other.print(false)
                                ),
                            });
                        }
                    };
                    let mut binders = binders;
                    let mut body = body;
                    let mut index = 0usize;
                    while index < binders.len() {
                        let binder = binders[index].clone();
                        let value = match binder.mode {
                            BinderMode::Explicit => match remaining.split_first() {
                                Some((argument, rest)) => {
                                    remaining = rest;
                                    supplied = supplied.saturating_add(1);
                                    let actual = self.infer(argument, scope)?;
                                    self.unify(&binder.ty, &actual)?;
                                    argument.clone()
                                }
                                None => {
                                    // Partial application: the rest of the
                                    // pi is the type.
                                    let rest: Vec<LseBinder> = binders[index..].to_vec();
                                    fty = Lse::Pi(rest, Box::new(body));
                                    return Ok(fty);
                                }
                            },
                            BinderMode::Implicit | BinderMode::Instance => self.fresh_meta(),
                        };
                        // Substitute the binder in the remaining binders and
                        // body.
                        for later in binders.iter_mut().skip(index.saturating_add(1)) {
                            later.ty = self.subst(&later.ty, &binder.name, &value);
                        }
                        body = self.subst(&body, &binder.name, &value);
                        index = index.saturating_add(1);
                    }
                    fty = body;
                }
                Ok(fty)
            }
            Lse::Pi(binders, body) => {
                let depth = scope.len();
                let mut result = Ok(Lse::SortProp);
                for binder in binders {
                    if let Err(error) = self.expect_type(&binder.ty, scope) {
                        result = Err(error);
                        break;
                    }
                    scope.push((binder.name.clone(), binder.ty.clone()));
                }
                if result.is_ok() {
                    result = self.expect_type(body, scope);
                }
                scope.truncate(depth);
                result
            }
            Lse::Lam(binders, body) => {
                let depth = scope.len();
                let mut result = Ok(Lse::SortProp);
                for binder in binders {
                    if let Err(error) = self.expect_type(&binder.ty, scope) {
                        result = Err(error);
                        break;
                    }
                    scope.push((binder.name.clone(), binder.ty.clone()));
                }
                if result.is_ok() {
                    result = self
                        .infer(body, scope)
                        .map(|body_ty| Lse::Pi(binders.clone(), Box::new(body_ty)));
                }
                scope.truncate(depth);
                result
            }
            Lse::Let {
                name,
                ty,
                value,
                body,
            } => {
                self.expect_type(ty, scope)?;
                let actual = self.infer(value, scope)?;
                self.unify(ty, &actual)?;
                scope.push((name.clone(), (**ty).clone()));
                let result = self.infer(body, scope);
                scope.pop();
                result
            }
        }
    }

    fn finish(self, ty: Lse) -> Checked {
        let ty = self.zonk(&ty);
        let literal_types = self
            .literal_metas
            .iter()
            .map(|meta| {
                let solved = self.zonk(&Lse::Local(meta.clone()));
                if self.has_unsolved_meta(&solved) {
                    None
                } else {
                    Some(solved)
                }
            })
            .collect();
        Checked { ty, literal_types }
    }
}

/// Flatten nested `pi`/`lam` chains into one binder list and final body.
fn flatten(expr: &Lse) -> (Vec<LseBinder>, Lse) {
    let mut binders = Vec::new();
    let mut current = expr;
    let is_pi = matches!(expr, Lse::Pi(..));
    loop {
        match current {
            Lse::Pi(bs, body) if is_pi => {
                binders.extend(bs.iter().cloned());
                current = body;
            }
            Lse::Lam(bs, body) if !is_pi => {
                binders.extend(bs.iter().cloned());
                current = body;
            }
            other => return (binders, other.clone()),
        }
    }
}

/// Check that `signature` is type-shaped (§13.7): a sort, a constant or
/// application whose type is a sort, or a `pi` over types into a sort or
/// type. Application arities are checked against the referenced entries'
/// signatures; literal types are recorded.
pub fn check_signature<'a>(
    signature: &Lse,
    lookup: &'a dyn Fn(&QualifiedId) -> ConstInfo<'a>,
) -> Result<Checked, TypeError> {
    let mut checker = Checker::new(lookup);
    let mut scope = Vec::new();
    let ty = checker.expect_type(signature, &mut scope)?;
    Ok(checker.finish(ty))
}

/// Check a defined value (§13.6): it must be well-typed under the
/// conservative rules and, when the entry has a signature, its inferred type
/// must be compatible with the signature (leading `lam` explicit binders
/// match the signature's `pi` explicit binders and the body agrees).
pub fn check_value<'a>(
    value: &Lse,
    signature: Option<&Lse>,
    lookup: &'a dyn Fn(&QualifiedId) -> ConstInfo<'a>,
) -> Result<Checked, TypeError> {
    let mut checker = Checker::new(lookup);
    let mut scope = Vec::new();
    let ty = checker.infer(value, &mut scope)?;
    if let Some(signature) = signature {
        checker.unify(signature, &ty).map_err(|error| TypeError {
            message: format!(
                "defined value `{}` does not match the signature `{}`: {}",
                value.print(false),
                signature.print(false),
                error.message
            ),
        })?;
    }
    Ok(checker.finish(ty))
}

#[cfg(test)]
mod tests {
    use super::*;

    const NAT: &str = "(const lexlean.std.nat::nat)";

    fn q(text: &str) -> QualifiedId {
        QualifiedId::parse(text).expect("qualified")
    }

    fn lookup(id: &QualifiedId) -> ConstInfo<'static> {
        use std::sync::OnceLock;
        static SIGS: OnceLock<BTreeMap<String, Lse>> = OnceLock::new();
        let sigs = SIGS.get_or_init(|| {
            let mut m = BTreeMap::new();
            m.insert("lexlean.std.nat::nat".to_owned(), parse("(sort (type 0))", 64).unwrap());
            m.insert(
                "lexlean.std.nat::add".to_owned(),
                parse(&format!("(pi ((explicit a {NAT}) (explicit b {NAT})) {NAT})"), 64).unwrap(),
            );
            m.insert(
                "lexlean.std.nat::list".to_owned(),
                parse("(pi ((explicit a (sort (type 0)))) (sort (type 0)))", 64).unwrap(),
            );
            m.insert(
                "lexlean.core::eq".to_owned(),
                parse(
                    "(pi ((implicit a (sort (type u))) (explicit b (local a)) (explicit c (local a))) (sort prop))",
                    64,
                )
                .unwrap(),
            );
            m
        });
        match sigs.get(&id.to_string()) {
            Some(signature) => ConstInfo::Signature {
                signature,
                defined: false,
            },
            None if id.entry == "the" => ConstInfo::NoSignature,
            None => ConstInfo::Missing,
        }
    }

    #[test]
    fn roundtrip_is_a_fixpoint() {
        let text = "(pi ((explicit n (const lexlean.std.nat::nat))) (app (const lexlean.core::eq (0)) (local n) (local n)))";
        let parsed = parse(text, 16).expect("parses");
        let printed = parsed.print(false);
        assert_eq!(printed, text);
        assert_eq!(parse(&printed, 16).unwrap(), parsed);
    }

    #[test]
    fn alpha_renaming_is_binding_ordered() {
        let a = parse(
            "(pi ((explicit n (sort prop)) (explicit m (sort prop))) (local m))",
            16,
        )
        .unwrap();
        let b = parse(
            "(pi ((explicit p (sort prop)) (explicit q (sort prop))) (local q))",
            16,
        )
        .unwrap();
        assert_eq!(a.print(true), b.print(true));
        assert_eq!(
            a.print(true),
            "(pi ((explicit x0 (sort prop)) (explicit x1 (sort prop))) (local x1))"
        );
    }

    #[test]
    fn depth_limit_is_a_limit_failure_not_an_abort() {
        let deep = format!(
            "{}(sort prop){}",
            "(app ".repeat(200_000),
            ")".repeat(200_000)
        );
        match parse(&deep, 1024) {
            Err(ParseError::DepthExceeded(1024)) => {}
            other => panic!("expected the depth limit, found {other:?}"),
        }
        let mut ok = "(sort prop)".to_owned();
        for _ in 0..500 {
            ok = format!("(app {ok} (sort prop))");
        }
        assert!(parse(&ok, 1024).is_ok());
        assert_eq!(parse(&ok, 400), Err(ParseError::DepthExceeded(400)));
    }

    #[test]
    fn syntax_errors_are_syntax() {
        assert!(matches!(parse("(nat 01)", 16), Err(ParseError::Syntax(_))));
        assert!(matches!(
            parse("(sort prop) extra", 16),
            Err(ParseError::Syntax(_))
        ));
        assert!(matches!(
            parse("(sort\tprop)", 16),
            Err(ParseError::Syntax(_))
        ));
        assert!(matches!(
            parse("(app (sort prop))", 16),
            Err(ParseError::Syntax(_))
        ));
    }

    #[test]
    fn scopes_are_lexical() {
        let unbound = parse("(local ghost)", 16).unwrap();
        assert!(unbound.check_scopes(&BTreeSet::new()).is_err());
        let ok = parse("(lam ((explicit x (sort prop))) (local x))", 16).unwrap();
        assert!(ok.check_scopes(&BTreeSet::new()).is_ok());
        let leaked = parse(
            "(app (lam ((explicit x (sort prop))) (local x)) (local x))",
            16,
        )
        .unwrap();
        assert!(leaked.check_scopes(&BTreeSet::new()).is_err());
        let universe = parse("(sort (type u))", 16).unwrap();
        assert!(universe.check_scopes(&BTreeSet::new()).is_err());
        assert!(universe
            .check_scopes(&["u".to_owned()].into_iter().collect())
            .is_ok());
    }

    #[test]
    fn signature_must_be_a_type() {
        let bad = parse("(nat 3)", 16).unwrap();
        assert!(check_signature(&bad, &lookup).is_err());
        let bad_const = parse("(app (const lexlean.std.nat::add) (nat 1) (nat 2))", 16).unwrap();
        assert!(check_signature(&bad_const, &lookup).is_err());
        let ok = parse(&format!("(pi ((explicit a {NAT})) (sort prop))"), 16).unwrap();
        assert!(check_signature(&ok, &lookup).is_ok());
        let ok_app = parse(&format!("(app (const lexlean.std.nat::list) {NAT})"), 16).unwrap();
        assert!(check_signature(&ok_app, &lookup).is_ok());
    }

    #[test]
    fn applications_respect_explicit_arity_and_literal_types() {
        let too_many = parse(
            &format!("(app (const lexlean.core::eq) {NAT} (nat 1) (nat 1))"),
            16,
        )
        .unwrap();
        let error = check_value(&too_many, None, &lookup).expect_err("three explicit args");
        assert!(
            error.message.contains("supplies 3 explicit arguments"),
            "{error}"
        );

        let ok = parse("(app (const lexlean.core::eq) (nat 1) (nat 2))", 16).unwrap();
        let checked = check_value(&ok, None, &lookup).expect("two explicit args");
        // The implicit type is unknown, so the literal types are unknown.
        assert_eq!(checked.literal_types, vec![None, None]);

        let typed = parse("(app (const lexlean.std.nat::add) (nat 1) (nat 2))", 16).unwrap();
        let checked = check_value(&typed, None, &lookup).expect("typed literals");
        let nat = parse(NAT, 16).unwrap();
        assert_eq!(
            checked.literal_types,
            vec![Some(nat.clone()), Some(nat.clone())]
        );
        assert_eq!(checked.ty, nat);

        let mismatch = parse(
            "(app (const lexlean.std.nat::add) (nat 1) (const lexlean.std.nat::nat))",
            16,
        )
        .unwrap();
        assert!(check_value(&mismatch, None, &lookup).is_err());
    }

    #[test]
    fn defined_values_match_signatures() {
        let signature = parse(
            &format!("(pi ((explicit a {NAT}) (explicit b {NAT})) {NAT})"),
            16,
        )
        .unwrap();
        let good = parse(
            &format!("(lam ((explicit x {NAT}) (explicit y {NAT})) (app (const lexlean.std.nat::add) (local y) (local x)))"),
            16,
        )
        .unwrap();
        assert!(check_value(&good, Some(&signature), &lookup).is_ok());
        let wrong_binder = parse(
            &format!("(lam ((explicit x {NAT}) (explicit y (sort prop))) (local x))"),
            16,
        )
        .unwrap();
        assert!(check_value(&wrong_binder, Some(&signature), &lookup).is_err());
        let wrong_body = parse(
            &format!("(lam ((explicit x {NAT}) (explicit y {NAT})) (sort prop))"),
            16,
        )
        .unwrap();
        assert!(check_value(&wrong_body, Some(&signature), &lookup).is_err());
        let by_reference = parse("(const lexlean.std.nat::add)", 16).unwrap();
        assert!(check_value(&by_reference, Some(&signature), &lookup).is_ok());
        let no_signature = parse("(const lexlean.core::the)", 16).unwrap();
        assert!(check_value(&no_signature, None, &lookup).is_err());
    }

    #[test]
    fn substitution_avoids_capture() {
        let mut checker = Checker::new(&lookup);
        let body = parse(
            "(pi ((explicit y (sort prop))) (app (local x) (local y)))",
            16,
        )
        .unwrap();
        let out = checker.subst(&body, "x", &Lse::Local("y".to_owned()));
        let printed = out.print(false);
        assert!(
            printed.starts_with("(pi ((explicit y#1 (sort prop))) (app (local y) (local y#1)))"),
            "{printed}"
        );
    }

    #[test]
    fn walkers_are_iterative_over_deep_trees() {
        // Build a deep tree programmatically (deeper than any thread stack
        // would tolerate recursively) and exercise every walker.
        let mut expr = Lse::SortProp;
        for _ in 0..200_000 {
            expr = Lse::App(Box::new(expr), vec![Lse::Nat("1".to_owned())]);
        }
        assert!(expr.check_scopes(&BTreeSet::new()).is_ok());
        assert_eq!(expr.referenced_consts().len(), 0);
        let printed = expr.print(true);
        assert!(printed.starts_with("(app (app "));
        // Dropping a deep tree must not recurse either.
        drop_iteratively(expr);
    }

    fn drop_iteratively(expr: Lse) {
        let mut stack = vec![expr];
        while let Some(node) = stack.pop() {
            match node {
                Lse::App(function, arguments) => {
                    stack.push(*function);
                    stack.extend(arguments);
                }
                Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
                    stack.push(*body);
                    stack.extend(binders.into_iter().map(|b| b.ty));
                }
                Lse::Let {
                    ty, value, body, ..
                } => {
                    stack.push(*ty);
                    stack.push(*value);
                    stack.push(*body);
                }
                _ => {}
            }
        }
    }

    #[test]
    fn identifiers_are_validated() {
        assert!(is_package_id("lexlean.std.nat"));
        assert!(!is_package_id("Lexlean"));
        assert!(!is_package_id("lex-lean.x"));
        assert!(is_entry_id("nat.add-zero"));
        assert!(!is_entry_id("nat..add"));
        assert!(!is_entry_id("1nat"));
        assert!(is_lse_identifier("x0"));
        assert!(!is_lse_identifier("_x"));
        assert!(q("a.b::c.d").to_string() == "a.b::c.d");
    }
}
