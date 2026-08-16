//! LexLean Semantic Expressions (SPEC.md §13.8).
//!
//! The S-expression interface language for entry signatures and defined
//! values. Comments and quoted strings do not exist; whitespace is ASCII
//! space or LF only.

use std::collections::BTreeSet;

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

/// Tokenize an S-expression: parens plus atoms, separated by one or more
/// ASCII spaces or LF; nothing else is whitespace and nothing is quoted.
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
            c if c.is_whitespace() => {
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

struct Parser {
    tokens: Vec<SexprToken>,
    at: usize,
}

impl Parser {
    fn peek(&self) -> Option<&SexprToken> {
        self.tokens.get(self.at)
    }

    fn next(&mut self) -> Result<SexprToken, String> {
        let token = self
            .tokens
            .get(self.at)
            .cloned()
            .ok_or_else(|| "unexpected end of expression".to_owned())?;
        self.at += 1;
        Ok(token)
    }

    fn expect_open(&mut self) -> Result<(), String> {
        match self.next()? {
            SexprToken::Open => Ok(()),
            other => Err(format!("expected `(`, found {other:?}")),
        }
    }

    fn expect_close(&mut self) -> Result<(), String> {
        match self.next()? {
            SexprToken::Close => Ok(()),
            other => Err(format!("expected `)`, found {other:?}")),
        }
    }

    fn atom(&mut self) -> Result<String, String> {
        match self.next()? {
            SexprToken::Atom(text) => Ok(text),
            other => Err(format!("expected an atom, found {other:?}")),
        }
    }

    fn universe(&mut self) -> Result<Universe, String> {
        match self.next()? {
            SexprToken::Atom(text) => {
                if text.bytes().all(|b| b.is_ascii_digit()) {
                    parse_decimal(&text).map(Universe::Num)
                } else if is_lse_identifier(&text) {
                    Ok(Universe::Var(text))
                } else {
                    Err(format!("`{text}` is not a universe"))
                }
            }
            SexprToken::Open => {
                let head = self.atom()?;
                let out = match head.as_str() {
                    "succ" => Universe::Succ(Box::new(self.universe()?)),
                    "max" => {
                        let mut items = vec![self.universe()?, self.universe()?];
                        while !matches!(self.peek(), Some(SexprToken::Close)) {
                            items.push(self.universe()?);
                        }
                        Universe::Max(items)
                    }
                    "imax" => {
                        Universe::IMax(Box::new(self.universe()?), Box::new(self.universe()?))
                    }
                    other => return Err(format!("`{other}` is not a universe form")),
                };
                self.expect_close()?;
                Ok(out)
            }
            SexprToken::Close => Err("expected a universe, found `)`".to_owned()),
        }
    }

    fn binder(&mut self) -> Result<LseBinder, String> {
        self.expect_open()?;
        let mode = match self.atom()?.as_str() {
            "explicit" => BinderMode::Explicit,
            "implicit" => BinderMode::Implicit,
            "instance" => BinderMode::Instance,
            other => return Err(format!("`{other}` is not a binder mode")),
        };
        let name = self.atom()?;
        if !is_lse_identifier(&name) {
            return Err(format!("`{name}` is not a valid local ID"));
        }
        let ty = self.expr()?;
        self.expect_close()?;
        Ok(LseBinder { mode, name, ty })
    }

    fn binder_list(&mut self) -> Result<Vec<LseBinder>, String> {
        self.expect_open()?;
        let mut binders = vec![self.binder()?];
        while !matches!(self.peek(), Some(SexprToken::Close)) {
            binders.push(self.binder()?);
        }
        self.expect_close()?;
        Ok(binders)
    }

    fn expr(&mut self) -> Result<Lse, String> {
        self.expect_open()?;
        let head = self.atom()?;
        let out = match head.as_str() {
            "sort" => match self.next()? {
                SexprToken::Atom(text) if text == "prop" => Lse::SortProp,
                SexprToken::Open => {
                    let keyword = self.atom()?;
                    if keyword != "type" {
                        return Err(format!("`{keyword}` is not a sort form"));
                    }
                    let universe = self.universe()?;
                    self.expect_close()?;
                    Lse::SortType(universe)
                }
                other => return Err(format!("invalid sort: {other:?}")),
            },
            "const" => {
                let id = QualifiedId::parse(&self.atom()?)?;
                let mut universes = Vec::new();
                if matches!(self.peek(), Some(SexprToken::Open)) {
                    self.expect_open()?;
                    universes.push(self.universe()?);
                    while !matches!(self.peek(), Some(SexprToken::Close)) {
                        universes.push(self.universe()?);
                    }
                    self.expect_close()?;
                }
                Lse::Const(id, universes)
            }
            "local" => {
                let name = self.atom()?;
                if !is_lse_identifier(&name) {
                    return Err(format!("`{name}` is not a valid local ID"));
                }
                Lse::Local(name)
            }
            "app" => {
                let function = self.expr()?;
                let mut arguments = vec![self.expr()?];
                while !matches!(self.peek(), Some(SexprToken::Close)) {
                    arguments.push(self.expr()?);
                }
                Lse::App(Box::new(function), arguments)
            }
            "pi" => Lse::Pi(self.binder_list()?, Box::new(self.expr()?)),
            "lam" => Lse::Lam(self.binder_list()?, Box::new(self.expr()?)),
            "let" => {
                let name = self.atom()?;
                if !is_lse_identifier(&name) {
                    return Err(format!("`{name}` is not a valid local ID"));
                }
                Lse::Let {
                    name,
                    ty: Box::new(self.expr()?),
                    value: Box::new(self.expr()?),
                    body: Box::new(self.expr()?),
                }
            }
            "nat" => {
                let digits = self.atom()?;
                parse_decimal(&digits)?;
                Lse::Nat(digits)
            }
            other => return Err(format!("`{other}` is not an LSE form")),
        };
        self.expect_close()?;
        Ok(out)
    }
}

fn parse_decimal(text: &str) -> Result<u64, String> {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("`{text}` is not a decimal"));
    }
    if text.len() > 1 && text.starts_with('0') {
        return Err(format!("`{text}` has a redundant leading zero"));
    }
    text.parse::<u64>()
        .map_err(|_| format!("`{text}` does not fit 64 bits"))
}

/// Parse one complete LSE expression.
pub fn parse(text: &str) -> Result<Lse, String> {
    let tokens = sexpr_tokens(text)?;
    let mut parser = Parser { tokens, at: 0 };
    let expr = parser.expr()?;
    if parser.at != parser.tokens.len() {
        return Err("trailing tokens after the expression".to_owned());
    }
    Ok(expr)
}

impl Lse {
    /// Check scoping: every `(local x)` resolves lexically and every
    /// universe variable is declared (§13.8).
    pub fn check_scopes(&self, universes: &BTreeSet<String>) -> Result<(), String> {
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
        fn walk(
            expr: &Lse,
            scope: &mut Vec<String>,
            universes: &BTreeSet<String>,
        ) -> Result<(), String> {
            match expr {
                Lse::SortProp | Lse::Nat(_) => Ok(()),
                Lse::SortType(u) => check_universe(u, universes),
                Lse::Const(_, args) => args.iter().try_for_each(|u| check_universe(u, universes)),
                Lse::Local(name) => {
                    if scope.iter().any(|s| s == name) {
                        Ok(())
                    } else {
                        Err(format!("local `{name}` is not in scope"))
                    }
                }
                Lse::App(function, arguments) => {
                    walk(function, scope, universes)?;
                    arguments.iter().try_for_each(|a| walk(a, scope, universes))
                }
                Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
                    let depth = scope.len();
                    for binder in binders {
                        walk(&binder.ty, scope, universes)?;
                        scope.push(binder.name.clone());
                    }
                    walk(body, scope, universes)?;
                    scope.truncate(depth);
                    Ok(())
                }
                Lse::Let {
                    name,
                    ty,
                    value,
                    body,
                } => {
                    walk(ty, scope, universes)?;
                    walk(value, scope, universes)?;
                    scope.push(name.clone());
                    walk(body, scope, universes)?;
                    scope.pop();
                    Ok(())
                }
            }
        }
        walk(self, &mut Vec::new(), universes)
    }

    /// Canonical printing (§13.8): one ASCII space between atoms, no
    /// redundant grouping. With `alpha_rename`, binders become `x0`, `x1`,
    /// ... in binding order, the form hashed for signature identity.
    #[must_use]
    pub fn print(&self, alpha_rename: bool) -> String {
        fn universe(u: &Universe, out: &mut String) {
            match u {
                Universe::Num(n) => out.push_str(&n.to_string()),
                Universe::Var(name) => out.push_str(name),
                Universe::Succ(inner) => {
                    out.push_str("(succ ");
                    universe(inner, out);
                    out.push(')');
                }
                Universe::Max(items) => {
                    out.push_str("(max");
                    for item in items {
                        out.push(' ');
                        universe(item, out);
                    }
                    out.push(')');
                }
                Universe::IMax(a, b) => {
                    out.push_str("(imax ");
                    universe(a, out);
                    out.push(' ');
                    universe(b, out);
                    out.push(')');
                }
            }
        }
        fn resolve(scope: &[(String, String)], name: &str) -> String {
            scope
                .iter()
                .rev()
                .find(|(original, _)| original == name)
                .map_or_else(|| name.to_owned(), |(_, renamed)| renamed.clone())
        }
        #[allow(clippy::too_many_lines)]
        fn walk(
            expr: &Lse,
            out: &mut String,
            scope: &mut Vec<(String, String)>,
            counter: &mut usize,
            rename: bool,
        ) {
            match expr {
                Lse::SortProp => out.push_str("(sort prop)"),
                Lse::SortType(u) => {
                    out.push_str("(sort (type ");
                    universe(u, out);
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
                            universe(arg, out);
                        }
                        out.push(')');
                    }
                    out.push(')');
                }
                Lse::Local(name) => {
                    out.push_str("(local ");
                    out.push_str(&if rename {
                        resolve(scope, name)
                    } else {
                        name.clone()
                    });
                    out.push(')');
                }
                Lse::App(function, arguments) => {
                    out.push_str("(app ");
                    walk(function, out, scope, counter, rename);
                    for argument in arguments {
                        out.push(' ');
                        walk(argument, out, scope, counter, rename);
                    }
                    out.push(')');
                }
                Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
                    out.push_str(if matches!(expr, Lse::Pi(..)) {
                        "(pi ("
                    } else {
                        "(lam ("
                    });
                    let depth = scope.len();
                    for (index, binder) in binders.iter().enumerate() {
                        if index > 0 {
                            out.push(' ');
                        }
                        out.push('(');
                        out.push_str(binder.mode.as_str());
                        out.push(' ');
                        let shown = if rename {
                            let fresh = format!("x{counter}");
                            *counter += 1;
                            fresh
                        } else {
                            binder.name.clone()
                        };
                        out.push_str(&shown);
                        out.push(' ');
                        walk(&binder.ty, out, scope, counter, rename);
                        out.push(')');
                        scope.push((binder.name.clone(), shown));
                    }
                    out.push_str(") ");
                    walk(body, out, scope, counter, rename);
                    out.push(')');
                    scope.truncate(depth);
                }
                Lse::Let {
                    name,
                    ty,
                    value,
                    body,
                } => {
                    out.push_str("(let ");
                    let shown = if rename {
                        let fresh = format!("x{counter}");
                        *counter += 1;
                        fresh
                    } else {
                        name.clone()
                    };
                    out.push_str(&shown);
                    out.push(' ');
                    walk(ty, out, scope, counter, rename);
                    out.push(' ');
                    walk(value, out, scope, counter, rename);
                    out.push(' ');
                    scope.push((name.clone(), shown));
                    walk(body, out, scope, counter, rename);
                    scope.pop();
                    out.push(')');
                }
                Lse::Nat(digits) => {
                    out.push_str("(nat ");
                    out.push_str(digits);
                    out.push(')');
                }
            }
        }
        let mut out = String::new();
        walk(self, &mut out, &mut Vec::new(), &mut 0, alpha_rename);
        out
    }

    /// Every qualified constant referenced by this expression.
    #[must_use]
    pub fn referenced_consts(&self) -> Vec<QualifiedId> {
        let mut out = Vec::new();
        fn walk(expr: &Lse, out: &mut Vec<QualifiedId>) {
            match expr {
                Lse::Const(id, _) => out.push(id.clone()),
                Lse::App(function, arguments) => {
                    walk(function, out);
                    for argument in arguments {
                        walk(argument, out);
                    }
                }
                Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
                    for binder in binders {
                        walk(&binder.ty, out);
                    }
                    walk(body, out);
                }
                Lse::Let {
                    ty, value, body, ..
                } => {
                    walk(ty, out);
                    walk(value, out);
                    walk(body, out);
                }
                Lse::SortProp | Lse::SortType(_) | Lse::Local(_) | Lse::Nat(_) => {}
            }
        }
        walk(self, &mut out);
        out
    }
}
