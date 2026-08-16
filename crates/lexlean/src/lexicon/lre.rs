//! LexLean Rendering Expressions (SPEC.md §13.9): the only way a glossary
//! entry influences canonical visible output. Raw TeX strings do not exist.

use crate::lexicon::lse::{sexpr_tokens, QualifiedId, SexprToken};

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

fn is_operator_name(text: &str) -> bool {
    let bytes = text.as_bytes();
    matches!(bytes.first(), Some(b) if b.is_ascii_alphabetic())
        && bytes[1..]
            .iter()
            .all(|b| b.is_ascii_alphanumeric() || *b == b'_')
}

fn is_token_id(text: &str) -> bool {
    let bytes = text.as_bytes();
    matches!(bytes.first(), Some(b) if b.is_ascii_lowercase())
        && bytes[1..]
            .iter()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || *b == b'-')
}

struct Parser {
    tokens: Vec<SexprToken>,
    at: usize,
}

impl Parser {
    fn next(&mut self) -> Result<SexprToken, String> {
        let token = self
            .tokens
            .get(self.at)
            .cloned()
            .ok_or_else(|| "unexpected end of render expression".to_owned())?;
        self.at += 1;
        Ok(token)
    }

    fn peek(&self) -> Option<&SexprToken> {
        self.tokens.get(self.at)
    }

    fn atom(&mut self) -> Result<String, String> {
        match self.next()? {
            SexprToken::Atom(text) => Ok(text),
            other => Err(format!("expected an atom, found {other:?}")),
        }
    }

    fn expect_close(&mut self) -> Result<(), String> {
        match self.next()? {
            SexprToken::Close => Ok(()),
            other => Err(format!("expected `)`, found {other:?}")),
        }
    }

    fn render(&mut self) -> Result<Render, String> {
        match self.next()? {
            SexprToken::Open => {}
            other => return Err(format!("expected `(`, found {other:?}")),
        }
        let head = self.atom()?;
        let out = match head.as_str() {
            "form" => {
                let entry = QualifiedId::parse(&self.atom()?)?;
                let form = self.atom()?;
                Render::Form { entry, form }
            }
            "self-form" => Render::SelfForm(self.atom()?),
            "slot" => {
                let digits = self.atom()?;
                let index: u32 = digits
                    .parse()
                    .map_err(|_| format!("`{digits}` is not a slot index"))?;
                Render::Slot(index)
            }
            "seq" => {
                let mut items = vec![self.render()?];
                while !matches!(self.peek(), Some(SexprToken::Close)) {
                    items.push(self.render()?);
                }
                Render::Seq(items)
            }
            "space" => Render::Space,
            "token" => {
                let id = self.atom()?;
                if !is_token_id(&id) {
                    return Err(format!("`{id}` is not a renderer-token ID"));
                }
                Render::Token(id)
            }
            "group" => Render::Group(Box::new(self.render()?)),
            "paren" => Render::Paren(Box::new(self.render()?)),
            "bracket" => Render::Bracket(Box::new(self.render()?)),
            "sub" => Render::Sub(Box::new(self.render()?), Box::new(self.render()?)),
            "sup" => Render::Sup(Box::new(self.render()?), Box::new(self.render()?)),
            "frac" => Render::Frac(Box::new(self.render()?), Box::new(self.render()?)),
            "operator-name" => {
                let name = self.atom()?;
                if !is_operator_name(&name) {
                    return Err(format!("`{name}` is not an operator name"));
                }
                Render::OperatorName(name)
            }
            other => return Err(format!("`{other}` is not an LRE form")),
        };
        self.expect_close()?;
        Ok(out)
    }
}

/// Parse one complete render expression.
pub fn parse(text: &str) -> Result<Render, String> {
    let tokens = sexpr_tokens(text)?;
    let mut parser = Parser { tokens, at: 0 };
    let render = parser.render()?;
    if parser.at != parser.tokens.len() {
        return Err("trailing tokens after the render expression".to_owned());
    }
    Ok(render)
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

    fn walk(&self, visit: &mut impl FnMut(&Render)) {
        visit(self);
        match self {
            Self::Seq(items) => {
                for item in items {
                    item.walk(visit);
                }
            }
            Self::Group(inner) | Self::Paren(inner) | Self::Bracket(inner) => inner.walk(visit),
            Self::Sub(a, b) | Self::Sup(a, b) | Self::Frac(a, b) => {
                a.walk(visit);
                b.walk(visit);
            }
            _ => {}
        }
    }
}
