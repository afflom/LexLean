//! Lexicon entries: schema, categories, frames, forms, denotations, and
//! per-entry validation (SPEC.md §13.2–§13.7, §16.11).

use std::collections::BTreeSet;

use serde::Deserialize;

use crate::artifact::content_id::Sha256Digest;
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::lexicon::lre::{self, Render};
use crate::lexicon::lse::{self, is_entry_id, Lse, QualifiedId};
use crate::source::atom::{Atom, AtomClass};

/// The exact language-1.0 categories (§13.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Category {
    /// Core-only source structure.
    Structural,
    /// Core-only determiner, connective, copula, or proof keyword.
    Grammar,
    /// A concept token allowed in titles and headings.
    LabelWord,
    /// A type-valued atom or phrase.
    TypeNoun,
    /// A term-valued atom.
    TermConstant,
    /// A function referenced by explicit call syntax.
    Function,
    /// One explicit surface argument, before it.
    PrefixFunction,
    /// One explicit surface argument, after it.
    PostfixFunction,
    /// Two explicit surface arguments.
    InfixFunction,
    /// Canonical "the SELF of ARG" function phrase.
    NounFunction,
    /// Canonical "the SELF of ARG and ARG" phrase.
    BinaryNounFunction,
    /// A proposition-valued atom.
    PredicateConstant,
    /// Canonical "ARG is SELF" predicate.
    AdjectivePredicate,
    /// Canonical "ARG SELF" predicate.
    IntransitivePredicate,
    /// Canonical "ARG SELF ARG" predicate.
    TransitivePredicate,
    /// Two-argument mathematical relation.
    InfixPredicate,
    /// A proof term or theorem reference.
    ProofConstant,
}

impl Category {
    /// Parse the schema token.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        Some(match text {
            "structural" => Self::Structural,
            "grammar" => Self::Grammar,
            "label-word" => Self::LabelWord,
            "type-noun" => Self::TypeNoun,
            "term-constant" => Self::TermConstant,
            "function" => Self::Function,
            "prefix-function" => Self::PrefixFunction,
            "postfix-function" => Self::PostfixFunction,
            "infix-function" => Self::InfixFunction,
            "noun-function" => Self::NounFunction,
            "binary-noun-function" => Self::BinaryNounFunction,
            "predicate-constant" => Self::PredicateConstant,
            "adjective-predicate" => Self::AdjectivePredicate,
            "intransitive-predicate" => Self::IntransitivePredicate,
            "transitive-predicate" => Self::TransitivePredicate,
            "infix-predicate" => Self::InfixPredicate,
            "proof-constant" => Self::ProofConstant,
            _ => return None,
        })
    }

    /// The schema token.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Structural => "structural",
            Self::Grammar => "grammar",
            Self::LabelWord => "label-word",
            Self::TypeNoun => "type-noun",
            Self::TermConstant => "term-constant",
            Self::Function => "function",
            Self::PrefixFunction => "prefix-function",
            Self::PostfixFunction => "postfix-function",
            Self::InfixFunction => "infix-function",
            Self::NounFunction => "noun-function",
            Self::BinaryNounFunction => "binary-noun-function",
            Self::PredicateConstant => "predicate-constant",
            Self::AdjectivePredicate => "adjective-predicate",
            Self::IntransitivePredicate => "intransitive-predicate",
            Self::TransitivePredicate => "transitive-predicate",
            Self::InfixPredicate => "infix-predicate",
            Self::ProofConstant => "proof-constant",
        }
    }

    /// May only `lexlean.core` declare this category (§13.3)?
    #[must_use]
    pub const fn core_only(self) -> bool {
        matches!(self, Self::Structural | Self::Grammar)
    }

    /// Does this category carry an LSE signature (§13.7)? Structural and
    /// grammar entries are structure, and label-words are concepts; none of
    /// the three is a semantic constant with an interface type.
    /// Implementation choice: §13.7 requires a signature of every *semantic*
    /// entry; a label-word denotes a concept reference (§29.1 "a defined
    /// concept reference to `add`") and is not itself typed, so it carries
    /// no signature and its defined value is checked for well-typedness
    /// only.
    #[must_use]
    pub const fn has_signature(self) -> bool {
        !matches!(self, Self::Structural | Self::Grammar | Self::LabelWord)
    }

    /// The channels in which a canonical source form is required (§13.5
    /// rule 7). Implementation choice: the specification fixes frames per
    /// category (§13.3, §13.4) but not the channel table; the table below
    /// follows the frames' surface patterns — prose frames (noun-of,
    /// adjective, ...) and prose atoms (type-noun, term-constant,
    /// label-word) need a text canonical form, mathematical frames (call,
    /// prefix, postfix, infix) and mathematical atoms (predicate-constant,
    /// proof-constant) need a math canonical form, structural/grammar
    /// entries are core structure with no required channel, and atoms that
    /// may live in either channel (type-noun, term-constant: `natural
    /// number`/`ℕ`, `zero`/`∅`) require a canonical form in at least one
    /// channel (checked separately by [`Category::needs_some_canonical`]).
    #[must_use]
    pub fn required_channels(self) -> &'static [Channel] {
        match self {
            Self::Structural | Self::Grammar | Self::TypeNoun | Self::TermConstant => &[],
            Self::LabelWord
            | Self::NounFunction
            | Self::BinaryNounFunction
            | Self::AdjectivePredicate
            | Self::IntransitivePredicate
            | Self::TransitivePredicate => &[Channel::Text],
            Self::Function
            | Self::PrefixFunction
            | Self::PostfixFunction
            | Self::InfixFunction
            | Self::InfixPredicate
            | Self::PredicateConstant
            | Self::ProofConstant => &[Channel::Math],
        }
    }
}

impl Category {
    /// Categories whose entries may be spelled in either channel and must
    /// therefore carry a canonical source form in at least one of them.
    #[must_use]
    pub const fn needs_some_canonical(self) -> bool {
        matches!(self, Self::TypeNoun | Self::TermConstant)
    }
}

/// The exact frame values (§13.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Frame {
    /// `SELF`.
    Atom,
    /// `SELF ( ARG_0, ..., ARG_n )`.
    Call,
    /// `SELF ARG_0`.
    Prefix,
    /// `ARG_0 SELF`.
    Postfix,
    /// `ARG_0 SELF ARG_1`.
    Infix,
    /// `the SELF of ARG_0`.
    NounOf,
    /// `the SELF of ARG_0 and ARG_1`.
    BinaryNounOf,
    /// `ARG_0 is SELF`.
    Adjective,
    /// `ARG_0 SELF`.
    Intransitive,
    /// `ARG_0 SELF ARG_1`.
    Transitive,
}

impl Frame {
    /// Parse the schema token.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        Some(match text {
            "atom" => Self::Atom,
            "call" => Self::Call,
            "prefix" => Self::Prefix,
            "postfix" => Self::Postfix,
            "infix" => Self::Infix,
            "noun-of" => Self::NounOf,
            "binary-noun-of" => Self::BinaryNounOf,
            "adjective" => Self::Adjective,
            "intransitive" => Self::Intransitive,
            "transitive" => Self::Transitive,
            _ => return None,
        })
    }

    /// The schema token.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Atom => "atom",
            Self::Call => "call",
            Self::Prefix => "prefix",
            Self::Postfix => "postfix",
            Self::Infix => "infix",
            Self::NounOf => "noun-of",
            Self::BinaryNounOf => "binary-noun-of",
            Self::Adjective => "adjective",
            Self::Intransitive => "intransitive",
            Self::Transitive => "transitive",
        }
    }

    /// The exact surface arity this frame fixes, or `None` for `call`
    /// (which takes the arity from the signature's explicit binders).
    #[must_use]
    pub const fn fixed_arity(self) -> Option<u32> {
        match self {
            Self::Atom => Some(0),
            Self::Prefix | Self::Postfix | Self::NounOf | Self::Adjective | Self::Intransitive => {
                Some(1)
            }
            Self::Infix | Self::BinaryNounOf | Self::Transitive => Some(2),
            Self::Call => None,
        }
    }
}

/// The exact category-to-frame compatibility (§13.3).
#[must_use]
pub fn frame_permitted(category: Category, frame: Frame, surface_arity: u32) -> bool {
    match category {
        Category::Structural
        | Category::Grammar
        | Category::LabelWord
        | Category::TypeNoun
        | Category::TermConstant
        | Category::PredicateConstant => frame == Frame::Atom,
        Category::Function => frame == Frame::Call,
        Category::PrefixFunction => frame == Frame::Prefix,
        Category::PostfixFunction => frame == Frame::Postfix,
        Category::InfixFunction | Category::InfixPredicate => frame == Frame::Infix,
        Category::NounFunction => frame == Frame::NounOf,
        Category::BinaryNounFunction => frame == Frame::BinaryNounOf,
        Category::AdjectivePredicate => frame == Frame::Adjective,
        Category::IntransitivePredicate => frame == Frame::Intransitive,
        Category::TransitivePredicate => frame == Frame::Transitive,
        Category::ProofConstant => {
            if surface_arity == 0 {
                frame == Frame::Atom
            } else {
                frame == Frame::Call
            }
        }
    }
}

/// A form channel (§13.5).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Channel {
    /// Prose.
    Text,
    /// Mathematical islands.
    Math,
    /// Both.
    Both,
}

impl Channel {
    /// Parse the schema token.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        Some(match text {
            "text" => Self::Text,
            "math" => Self::Math,
            "both" => Self::Both,
            _ => return None,
        })
    }

    /// Does a form with this channel serve channel `wanted`?
    #[must_use]
    pub fn covers(self, wanted: Channel) -> bool {
        self == Channel::Both || self == wanted
    }
}

/// The closed feature vocabulary (§13.5).
pub const FEATURES: [&str; 6] = [
    "singular",
    "plural",
    "sentence-case",
    "lower-case",
    "article-a",
    "article-an",
];

/// One surface form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Form {
    /// Local form ID.
    pub id: String,
    /// The channel.
    pub channel: Channel,
    /// The exact normalized spelling.
    pub surface: String,
    /// The scanned primitive atoms of the surface.
    pub atoms: Vec<Atom>,
    /// Is this the canonical source form for its channel?
    pub canonical_source: bool,
    /// Explicit inflection features, sorted and unique.
    pub features: Vec<String>,
}

/// A validated denotation (§13.6).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Denotation {
    /// A core constructor; only `lexlean.core` may use it.
    Core {
        /// The constructor name, e.g. `logic.eq`.
        constructor: String,
    },
    /// An external Lean constant.
    Lean {
        /// The Lean module to import.
        module: String,
        /// The fully qualified Lean name.
        name: String,
    },
    /// A LexLean document declaration.
    Document {
        /// The source module name.
        module: String,
        /// The component ID.
        component: String,
    },
    /// A defined lexicon value.
    Defined {
        /// The parsed value.
        value: Lse,
        /// The canonical text, for hashing.
        text: String,
    },
}

/// An eliminator constructor row (§16.11).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EliminatorConstructor {
    /// The constructor's glossary entry.
    pub entry: QualifiedId,
    /// The constructor's Lean name.
    pub lean_name: String,
    /// Field binder names, in order.
    pub fields: Vec<String>,
    /// Induction-hypothesis binder names, in order.
    pub induction_hypotheses: Vec<String>,
}

/// An eliminator descriptor (§16.11): an interface, not trusted proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Eliminator {
    /// The cases eliminator's Lean name.
    pub cases_lean_name: String,
    /// The induction eliminator's Lean name.
    pub induction_lean_name: String,
    /// Every constructor, in canonical descriptor order.
    pub constructors: Vec<EliminatorConstructor>,
}

/// One validated lexicon entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// Local entry ID.
    pub id: String,
    /// The category.
    pub category: Category,
    /// The frame.
    pub frame: Frame,
    /// Explicit surface arity.
    pub surface_arity: u32,
    /// The parsed signature, when the category has one.
    pub signature: Option<Lse>,
    /// Canonical alpha-renamed signature text.
    pub signature_canonical: Option<String>,
    /// SHA-256 of the canonical signature (§13.7).
    pub signature_hash: Option<Sha256Digest>,
    /// Declared universe variables, sorted.
    pub universes: Vec<String>,
    /// Pratt precedence for prefix, postfix, and infix frames.
    pub precedence: Option<u8>,
    /// Associativity for infix frames.
    pub associativity: Option<Associativity>,
    /// The denotation.
    pub denotation: Denotation,
    /// Surface forms.
    pub forms: Vec<Form>,
    /// Canonical math render template.
    pub render_math: Option<Render>,
    /// Canonical text render template.
    pub render_text: Option<Render>,
    /// The calculation descriptor, for relations that authorize `calc`.
    pub calculation: bool,
    /// The eliminator descriptor, for types that authorize cases and
    /// induction.
    pub eliminator: Option<Eliminator>,
}

/// Infix associativity (§15.5).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Associativity {
    /// Left-associative.
    Left,
    /// Right-associative.
    Right,
    /// Nonassociative: chains need explicit parentheses.
    None,
}

impl Associativity {
    /// Parse the schema token.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        Some(match text {
            "left" => Self::Left,
            "right" => Self::Right,
            "none" => Self::None,
            _ => return None,
        })
    }
}

/// Renderer-safe text punctuation (§13.5 rule 4, §15.3): the ASCII symbols a
/// non-core canonical text form may contain besides words and single
/// spaces. Each is safe in LaTeX text mode and is a core punctuation entry
/// or an ordinary prose mark. Shared with the output side: the LaTeX
/// backend's form-surface emission must refuse anything outside
/// [`surface_safety`].
pub const TEXT_SAFE_PUNCTUATION: [&str; 6] = [":", "-", ",", ".", ";", "'"];

/// Printable ASCII symbols that are never renderer-safe in a form surface:
/// TeX specials, braces (delimiter class), quotes, and the backtick.
pub const RENDERER_UNSAFE_ASCII: [&str; 12] =
    ["\\", "%", "$", "#", "&", "~", "^", "_", "{", "}", "\"", "`"];

/// Is `scalar` a renderer-safe non-ASCII mathematical symbol (§13.5 rule
/// 5)? An explicit allow-list of scalar ranges, never a host Unicode class:
/// Latin-1 mathematical marks, Greek letters, letterlike symbols, arrows,
/// mathematical operators, ceiling/floor and angle brackets, the
/// miscellaneous and supplemental mathematical symbol blocks, prime and
/// ellipsis marks, and mathematical alphanumerics. Combining marks (U+0300–
/// U+036F, U+20D0–U+20FF), format scalars (U+200B–U+200F, U+2028–U+202E,
/// U+2060–U+206F, U+FEFF), and everything else are unsafe.
#[must_use]
pub fn is_math_safe_scalar(scalar: char) -> bool {
    let code = u32::from(scalar);
    matches!(code, 0x00AC | 0x00B1 | 0x00B7 | 0x00D7 | 0x00F7)
        || (0x0391..=0x03A9).contains(&code) && code != 0x03A2
        || (0x03B1..=0x03C9).contains(&code)
        || matches!(code, 0x2026 | 0x2032..=0x2034)
        || (0x2100..=0x214F).contains(&code)
        || (0x2190..=0x21FF).contains(&code)
        || (0x2200..=0x22FF).contains(&code)
        || (0x2308..=0x230B).contains(&code)
        || (0x27C0..=0x27EF).contains(&code)
        || (0x2980..=0x29FF).contains(&code)
        || (0x2A00..=0x2AFF).contains(&code)
        || (0x1D400..=0x1D7FF).contains(&code)
}

/// The single renderer-safety predicate for form surfaces (§13.5 rules 4
/// and 5), shared by canonical-form validation, LRE form-reference
/// validation, and the backend's form-surface emission.
///
/// - text channel: ASCII words, single spaces, and [`TEXT_SAFE_PUNCTUATION`];
/// - math channel: ASCII words, single spaces, printable ASCII symbols
///   outside [`RENDERER_UNSAFE_ASCII`], the delimiters `(`, `)`, `[`, `]`,
///   and non-ASCII scalars accepted by [`is_math_safe_scalar`];
/// - both channels: both predicates.
///
/// Numerals are not renderer-safe in text and as the first atom of a math surface (a
/// leading numeral would shadow the core numeral constructor); inside a math
/// surface (`x1`) they are ordinary identifier material. Controls are never
/// safe (raw TeX), braces are never safe (structure).
pub fn surface_safety(atoms: &[Atom], channel: Channel) -> Result<(), String> {
    for (index, atom) in atoms.iter().enumerate() {
        let text_ok = match atom.class {
            AtomClass::Word | AtomClass::Whitespace => true,
            AtomClass::AsciiSymbol => TEXT_SAFE_PUNCTUATION.contains(&atom.text.as_str()),
            AtomClass::Numeral
            | AtomClass::Delimiter
            | AtomClass::UnicodeSymbol
            | AtomClass::Control => false,
        };
        let math_ok = match atom.class {
            AtomClass::Word | AtomClass::Whitespace => true,
            AtomClass::AsciiSymbol => !RENDERER_UNSAFE_ASCII.contains(&atom.text.as_str()),
            AtomClass::Delimiter => matches!(atom.text.as_str(), "(" | ")" | "[" | "]"),
            AtomClass::UnicodeSymbol => atom.text.chars().all(is_math_safe_scalar),
            AtomClass::Numeral => index > 0,
            AtomClass::Control => false,
        };
        let ok = match channel {
            Channel::Text => text_ok,
            Channel::Math => math_ok,
            Channel::Both => text_ok && math_ok,
        };
        if !ok {
            return Err(format!(
                "`{}` ({}) is not renderer-safe in the {} channel",
                atom.text,
                atom.class.as_str(),
                match channel {
                    Channel::Text => "text",
                    Channel::Math => "math",
                    Channel::Both => "text and math",
                }
            ));
        }
    }
    Ok(())
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawEntry {
    spec: String,
    id: String,
    category: String,
    signature: Option<String>,
    universes: Option<Vec<String>>,
    surface_arity: u32,
    frame: String,
    precedence: Option<u32>,
    associativity: Option<String>,
    denotation: RawDenotation,
    form: Vec<RawForm>,
    render: Option<RawRender>,
    calculation: Option<RawCalculation>,
    eliminator: Option<RawEliminator>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawDenotation {
    kind: String,
    constructor: Option<String>,
    module: Option<String>,
    name: Option<String>,
    component: Option<String>,
    value: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawForm {
    id: String,
    channel: String,
    surface: String,
    canonical_source: bool,
    features: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawRender {
    math: Option<String>,
    text: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawCalculation {
    kind: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawEliminator {
    cases_lean_name: String,
    induction_lean_name: String,
    constructor: Vec<RawEliminatorConstructor>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawEliminatorConstructor {
    entry: String,
    lean_name: String,
    fields: Vec<String>,
    induction_hypotheses: Vec<String>,
}

/// The conservative ASCII Lean-name grammar (§13.6): dot-separated segments
/// of ASCII letters, digits, and underscores, each starting with a letter or
/// underscore.
#[must_use]
pub fn is_lean_name(text: &str) -> bool {
    !text.is_empty()
        && text.split('.').all(|segment| {
            let bytes = segment.as_bytes();
            matches!(bytes.first(), Some(b) if b.is_ascii_alphabetic() || *b == b'_')
                && bytes[1..]
                    .iter()
                    .all(|b| b.is_ascii_alphanumeric() || *b == b'_')
        })
}

fn error(path: &str, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLR3004"), message).with_span(crate::diagnostic::Span::whole_file(path))
}

fn form_unsafe(path: &str, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLR3006"), message).with_span(crate::diagnostic::Span::whole_file(path))
}

fn limit(path: &str, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLS8002"), message).with_span(crate::diagnostic::Span::whole_file(path))
}

/// The per-package context entry validation needs.
#[derive(Debug, Clone, Copy)]
pub struct EntryContext<'a> {
    /// Whether the containing package is `lexlean.core`.
    pub is_core: bool,
    /// The §12.4 always-forbidden controls, from `language/bootstrap.toml`.
    pub forbidden_controls: &'a [String],
    /// The configured `max_scope_depth`, bounding LSE/LRE nesting.
    pub max_scope_depth: u64,
}

/// Parse an LSE field, mapping a depth failure to `LLS8002` and any other
/// failure to `LLR3004`.
fn parse_lse_field(
    path: &str,
    what: &str,
    text: &str,
    max_scope_depth: u64,
) -> Result<Lse, Diagnostic> {
    lse::parse(text, max_scope_depth).map_err(|parse_error| match parse_error {
        lse::ParseError::DepthExceeded(configured) => limit(
            path,
            format!("{what}: max_scope_depth exceeded: configured {configured}"),
        ),
        lse::ParseError::Syntax(message) => error(path, format!("invalid {what} LSE: {message}")),
    })
}

/// Parse and validate one entry file (§13.2–§13.7).
#[allow(clippy::too_many_lines)]
pub fn parse_entry(
    path: &str,
    text: &str,
    ctx: &EntryContext<'_>,
) -> Result<Entry, Vec<Diagnostic>> {
    let is_core = ctx.is_core;
    let mut diagnostics = Vec::new();

    let raw: RawEntry = match toml::from_str(text) {
        Ok(raw) => raw,
        Err(parse_error) => {
            return Err(vec![error(
                path,
                format!("invalid entry file: {parse_error}"),
            )]);
        }
    };
    if raw.spec != "lexlean/entry/1" {
        return Err(vec![Diagnostic::new(
            code!("LLC0103"),
            format!("unsupported entry schema `{}`", raw.spec),
        )
        .with_span(crate::diagnostic::Span::whole_file(path))]);
    }
    if !is_entry_id(&raw.id) {
        diagnostics.push(error(path, format!("`{}` is not a valid entry ID", raw.id)));
    }
    let Some(category) = Category::parse(&raw.category) else {
        return Err(vec![error(
            path,
            format!("`{}` is not a category", raw.category),
        )]);
    };
    let Some(frame) = Frame::parse(&raw.frame) else {
        return Err(vec![error(path, format!("`{}` is not a frame", raw.frame))]);
    };
    if category.core_only() && !is_core {
        diagnostics.push(error(
            path,
            format!("a non-core entry cannot use category `{}`", raw.category),
        ));
    }
    if !frame_permitted(category, frame, raw.surface_arity) {
        diagnostics.push(error(
            path,
            format!(
                "category `{}` does not permit frame `{}`",
                raw.category, raw.frame
            ),
        ));
    }
    if let Some(fixed) = frame.fixed_arity() {
        if raw.surface_arity != fixed {
            diagnostics.push(error(
                path,
                format!(
                    "frame `{}` fixes surface_arity {fixed}, found {}",
                    raw.frame, raw.surface_arity
                ),
            ));
        }
    } else if raw.surface_arity == 0 {
        diagnostics.push(error(path, "a call frame needs surface_arity >= 1"));
    }

    // Precedence and associativity apply exactly to the Pratt frames.
    let needs_precedence = matches!(frame, Frame::Prefix | Frame::Postfix | Frame::Infix);
    let precedence = match (raw.precedence, needs_precedence) {
        (Some(value), true) => match u8::try_from(value) {
            Ok(p) => Some(p),
            Err(_) => {
                diagnostics.push(error(path, "precedence is 0..255"));
                None
            }
        },
        (None, true) => {
            diagnostics.push(error(path, "this frame requires a precedence"));
            None
        }
        (Some(_), false) => {
            diagnostics.push(error(path, "precedence does not apply to this frame"));
            None
        }
        (None, false) => None,
    };
    let associativity = match (&raw.associativity, frame) {
        (Some(text), Frame::Infix) => match Associativity::parse(text) {
            Some(assoc) => Some(assoc),
            None => {
                diagnostics.push(error(path, "associativity is left, right, or none"));
                None
            }
        },
        (None, Frame::Infix) => {
            diagnostics.push(error(path, "an infix frame requires an associativity"));
            None
        }
        (Some(_), _) => {
            diagnostics.push(error(path, "associativity applies only to infix frames"));
            None
        }
        (None, _) => None,
    };

    // Universes and signature.
    let universes: Vec<String> = raw.universes.clone().unwrap_or_default();
    let universe_set: BTreeSet<String> = universes.iter().cloned().collect();
    if universes.len() != universe_set.len() || !universes.windows(2).all(|pair| pair[0] < pair[1])
    {
        diagnostics.push(error(path, "universes must be sorted and unique"));
    }
    for name in &universes {
        if !lse::is_lse_identifier(name) {
            diagnostics.push(error(path, format!("`{name}` is not a universe name")));
        }
    }
    let mut signature = None;
    let mut signature_canonical = None;
    let mut signature_hash = None;
    match (&raw.signature, category.has_signature()) {
        (Some(text), true) => match parse_lse_field(path, "signature", text, ctx.max_scope_depth) {
            Ok(parsed) => {
                if let Err(scope_error) = parsed.check_scopes(&universe_set) {
                    diagnostics.push(error(path, format!("invalid signature: {scope_error}")));
                }
                // The signature fixes the surface arity (§13.4, §13.9):
                // every explicit binder of the outer pi is one surface slot.
                let explicit = parsed.outer_explicit_binders();
                if u64::from(raw.surface_arity) != explicit as u64 {
                    diagnostics.push(error(
                        path,
                        format!(
                            "`{}`: surface_arity {} does not match the {explicit} explicit binder{} of the signature's outer pi",
                            raw.id,
                            raw.surface_arity,
                            if explicit == 1 { "" } else { "s" }
                        ),
                    ));
                }
                let canonical = parsed.print(true);
                signature_hash = Some(Sha256Digest::of(canonical.as_bytes()));
                signature_canonical = Some(canonical);
                signature = Some(parsed);
            }
            Err(diagnostic) => diagnostics.push(diagnostic),
        },
        (None, true) => {
            diagnostics.push(error(
                path,
                "every semantic entry has a complete LSE signature",
            ));
        }
        (Some(_), false) => {
            diagnostics.push(error(
                path,
                format!("category `{}` does not carry a signature", raw.category),
            ));
        }
        (None, false) => {
            if raw.universes.is_some() {
                diagnostics.push(error(path, "universes apply only with a signature"));
            }
        }
    }

    // The denotation: exactly the fields of its kind (§13.6), no prose
    // fields anywhere (unknown fields are already a parse failure).
    let d = &raw.denotation;
    let field_count = usize::from(d.constructor.is_some())
        + usize::from(d.module.is_some())
        + usize::from(d.name.is_some())
        + usize::from(d.component.is_some())
        + usize::from(d.value.is_some());
    let denotation = match d.kind.as_str() {
        "core" => {
            if !is_core {
                diagnostics.push(error(path, "only lexlean.core may use a core denotation"));
            }
            match (&d.constructor, field_count) {
                (Some(constructor), 1) if is_entry_id(constructor) => Denotation::Core {
                    constructor: constructor.clone(),
                },
                _ => {
                    diagnostics.push(error(path, "a core denotation has exactly `constructor`"));
                    Denotation::Core {
                        constructor: String::new(),
                    }
                }
            }
        }
        "lean" => match (&d.module, &d.name, field_count) {
            (Some(module), Some(name), 2) if is_lean_name(module) && is_lean_name(name) => {
                Denotation::Lean {
                    module: module.clone(),
                    name: name.clone(),
                }
            }
            _ => {
                diagnostics.push(error(
                    path,
                    "a lean denotation has exactly `module` and `name` in the conservative ASCII Lean-name grammar",
                ));
                Denotation::Lean {
                    module: String::new(),
                    name: String::new(),
                }
            }
        },
        "document" => match (&d.module, &d.component, field_count) {
            (Some(module), Some(component), 2) => Denotation::Document {
                module: module.clone(),
                component: component.clone(),
            },
            _ => {
                diagnostics.push(error(
                    path,
                    "a document denotation has exactly `module` and `component`",
                ));
                Denotation::Document {
                    module: String::new(),
                    component: String::new(),
                }
            }
        },
        "defined" => match (&d.value, field_count) {
            (Some(value_text), 1) => {
                match parse_lse_field(path, "defined value", value_text, ctx.max_scope_depth) {
                    Ok(value) => {
                        if let Err(scope_error) = value.check_scopes(&universe_set) {
                            diagnostics
                                .push(error(path, format!("invalid defined value: {scope_error}")));
                        }
                        Denotation::Defined {
                            text: value.print(true),
                            value,
                        }
                    }
                    Err(diagnostic) => {
                        diagnostics.push(diagnostic);
                        Denotation::Defined {
                            value: Lse::SortProp,
                            text: String::new(),
                        }
                    }
                }
            }
            _ => {
                diagnostics.push(error(path, "a defined denotation has exactly `value`"));
                Denotation::Defined {
                    value: Lse::SortProp,
                    text: String::new(),
                }
            }
        },
        other => {
            diagnostics.push(error(path, format!("`{other}` is not a denotation kind")));
            Denotation::Core {
                constructor: String::new(),
            }
        }
    };

    // Forms (§13.5).
    let mut forms = Vec::new();
    let mut form_ids = BTreeSet::new();
    if raw.form.is_empty() {
        diagnostics.push(error(path, "an entry declares at least one form"));
    }
    for raw_form in &raw.form {
        if !lre::is_form_id(&raw_form.id) {
            diagnostics.push(error(
                path,
                format!("`{}` is not a form ID ([a-z][a-z0-9-]*)", raw_form.id),
            ));
        }
        if !form_ids.insert(raw_form.id.clone()) {
            diagnostics.push(error(path, format!("duplicate form ID `{}`", raw_form.id)));
        }
        let Some(channel) = Channel::parse(&raw_form.channel) else {
            diagnostics.push(error(path, "a form channel is text, math, or both"));
            continue;
        };
        let surface = &raw_form.surface;
        if surface.is_empty()
            || surface.starts_with(' ')
            || surface.ends_with(' ')
            || surface.contains("  ")
            || surface.contains('\n')
        {
            diagnostics.push(error(
                path,
                format!("form `{}`: leading, trailing, or repeated whitespace in the surface is forbidden", raw_form.id),
            ));
            continue;
        }
        // A surface is parsed into primitive atoms at package-load time. A
        // surface is bounded only by the file it lives in; each scalar is at
        // most one atom, so the scanner's atom budget is the scalar count.
        let scalar_count = surface.chars().count() as u64;
        let atoms = match crate::source::scan::scan("<form>", surface, scalar_count) {
            Ok(atoms) => atoms,
            Err(scan_error) => {
                diagnostics.push(error(
                    path,
                    format!(
                        "form `{}`: surface does not scan: {}",
                        raw_form.id, scan_error.message
                    ),
                ));
                continue;
            }
        };
        for atom in &atoms {
            if atom.class == AtomClass::Control
                && ctx
                    .forbidden_controls
                    .iter()
                    .any(|forbidden| forbidden == &atom.text)
            {
                diagnostics.push(error(
                    path,
                    format!(
                        "form `{}` declares the always-forbidden control `{}` (§12.4)",
                        raw_form.id, atom.text
                    ),
                ));
            }
        }
        let is_control_form = atoms.iter().any(|atom| atom.class == AtomClass::Control);
        if is_control_form && raw_form.canonical_source && !is_core {
            diagnostics.push(error(
                path,
                format!(
                    "form `{}`: control-sequence forms are aliases only for non-core entries",
                    raw_form.id
                ),
            ));
        }
        if !is_core {
            // Every non-core form is either renderer-safe (it may be
            // rendered as the selected spelling of the entry) or exactly one
            // control-sequence alias such as `\N` (§13.5 rule 3: an input
            // spelling that is never rendered). A canonical form must be
            // renderer-safe (§13.5 rules 4-5).
            let single_control_alias = !raw_form.canonical_source
                && atoms.len() == 1
                && atoms[0].class == AtomClass::Control;
            if !single_control_alias {
                if let Err(reason) = surface_safety(&atoms, channel) {
                    diagnostics.push(form_unsafe(
                        path,
                        format!(
                            "form `{}`: the {} surface `{}` is not renderer-safe: {reason}",
                            raw_form.id,
                            if raw_form.canonical_source {
                                "canonical"
                            } else {
                                "alias"
                            },
                            raw_form.surface
                        ),
                    ));
                }
            }
        }
        let features = raw_form.features.clone();
        let feature_set: BTreeSet<&String> = features.iter().collect();
        if feature_set.len() != features.len() || !features.windows(2).all(|pair| pair[0] < pair[1])
        {
            diagnostics.push(error(
                path,
                format!("form `{}`: features must be sorted and unique", raw_form.id),
            ));
        }
        for feature in &features {
            if !FEATURES.contains(&feature.as_str()) {
                diagnostics.push(error(
                    path,
                    format!("form `{}`: `{feature}` is not a feature", raw_form.id),
                ));
            }
        }
        forms.push(Form {
            id: raw_form.id.clone(),
            channel,
            surface: surface.clone(),
            atoms,
            canonical_source: raw_form.canonical_source,
            features,
        });
    }

    // Exactly one canonical source form per channel (§13.5 rules 7).
    if category.needs_some_canonical() && !forms.iter().any(|form| form.canonical_source) {
        diagnostics.push(error(
            path,
            format!(
                "category `{}` requires a canonical source form in the text or the math channel",
                category.as_str()
            ),
        ));
    }
    for channel in [Channel::Text, Channel::Math] {
        let canonical_count = forms
            .iter()
            .filter(|form| form.canonical_source && form.channel.covers(channel))
            .count();
        let channel_name = if channel == Channel::Text {
            "text"
        } else {
            "math"
        };
        if canonical_count > 1 {
            diagnostics.push(error(
                path,
                format!("more than one canonical source form for the {channel_name} channel"),
            ));
        }
        if category.required_channels().contains(&channel) && canonical_count == 0 {
            diagnostics.push(error(
                path,
                format!(
                    "category `{}` requires a canonical source form in the {channel_name} channel",
                    category.as_str()
                ),
            ));
        }
    }

    // Renders (§13.9). A math frame with surface arguments requires a math
    // template; slot use is exact; a text template applies only to entries
    // whose category has a text canonical form (§13.2: inapplicable fields
    // are forbidden).
    let mut render_math = None;
    let mut render_text = None;
    if let Some(raw_render) = &raw.render {
        if matches!(category, Category::Structural | Category::Grammar) {
            diagnostics.push(error(
                path,
                "structural and grammar entries do not carry render templates",
            ));
        }
        if raw_render.text.is_some()
            && !category.required_channels().contains(&Channel::Text)
            && !(category.needs_some_canonical()
                && forms
                    .iter()
                    .any(|form| form.canonical_source && form.channel.covers(Channel::Text)))
        {
            diagnostics.push(error(
                path,
                format!(
                    "category `{}` has no text canonical form, so a text render does not apply",
                    category.as_str()
                ),
            ));
        }
        for (channel, text_value, slot) in [
            (Channel::Math, &raw_render.math, &mut render_math),
            (Channel::Text, &raw_render.text, &mut render_text),
        ] {
            let channel_name = if channel == Channel::Text {
                "text"
            } else {
                "math"
            };
            let Some(render_source) = text_value else {
                continue;
            };
            match lre::parse(render_source, ctx.max_scope_depth) {
                Ok(render) => {
                    let mut used: Vec<u32> = render.slots();
                    used.sort_unstable();
                    let expected: Vec<u32> = (0..raw.surface_arity).collect();
                    if used != expected {
                        diagnostics.push(error(
                            path,
                            format!(
                                "{channel_name} render must use every slot 0..{} exactly once",
                                raw.surface_arity
                            ),
                        ));
                    }
                    if let Some(problem) = render.script_operand_error() {
                        diagnostics.push(error(path, format!("{channel_name} render: {problem}")));
                    }
                    for self_form in render.self_form_refs() {
                        match forms.iter().find(|form| form.id == self_form) {
                            None => diagnostics.push(error(
                                path,
                                format!(
                                    "{channel_name} render references unknown self form `{self_form}`"
                                ),
                            )),
                            Some(form) => {
                                if !form.channel.covers(channel) {
                                    diagnostics.push(error(
                                        path,
                                        format!(
                                            "{channel_name} render references self form `{self_form}`, which is not a {channel_name} form"
                                        ),
                                    ));
                                }
                                // Every form an LRE emits must be renderer-
                                // safe, canonical or not (§13.9: raw TeX
                                // strings do not exist).
                                if let Err(reason) = surface_safety(&form.atoms, form.channel) {
                                    diagnostics.push(form_unsafe(
                                        path,
                                        format!(
                                            "{channel_name} render references self form `{self_form}` whose surface `{}` is not renderer-safe: {reason}",
                                            form.surface
                                        ),
                                    ));
                                }
                            }
                        }
                    }
                    *slot = Some(render);
                }
                Err(lse::ParseError::DepthExceeded(configured)) => {
                    diagnostics.push(limit(
                        path,
                        format!(
                            "{channel_name} render: max_scope_depth exceeded: configured {configured}"
                        ),
                    ));
                }
                Err(lse::ParseError::Syntax(message)) => {
                    diagnostics.push(error(
                        path,
                        format!("invalid {channel_name} LRE: {message}"),
                    ));
                }
            }
        }
    }
    let needs_math_render = matches!(
        frame,
        Frame::Call | Frame::Prefix | Frame::Postfix | Frame::Infix
    );
    if needs_math_render && render_math.is_none() {
        diagnostics.push(error(
            path,
            "a math frame with surface arguments requires a canonical math render",
        ));
    }

    // Calculation descriptor (§16.10): only a relation authorizes calc.
    let calculation = match &raw.calculation {
        Some(raw_calculation) => {
            if raw_calculation.kind != "equality" {
                diagnostics.push(error(
                    path,
                    "language 1.0 ships exactly the equality calculation descriptor",
                ));
            }
            if category != Category::InfixPredicate {
                diagnostics.push(error(
                    path,
                    "a calculation descriptor belongs to an infix relation",
                ));
            }
            true
        }
        None => false,
    };

    // Eliminator descriptor (§16.11): a type entry — any entry whose
    // signature results in a sort, so type-nouns and sort-valued
    // functions/predicates such as conjunction — authorizes cases and
    // induction.
    let eliminator = match &raw.eliminator {
        Some(raw_eliminator) => {
            let sort_valued = signature
                .as_ref()
                .is_some_and(|sig| matches!(sig.result(), Lse::SortProp | Lse::SortType(_)));
            if !sort_valued {
                diagnostics.push(error(
                    path,
                    format!(
                        "`{}`: an eliminator descriptor belongs to a type entry, whose signature results in a sort",
                        raw.id
                    ),
                ));
            }
            for (what, name) in [
                ("cases_lean_name", &raw_eliminator.cases_lean_name),
                ("induction_lean_name", &raw_eliminator.induction_lean_name),
            ] {
                if !is_lean_name(name) {
                    diagnostics.push(error(
                        path,
                        format!("eliminator {what} `{name}` is not a Lean name"),
                    ));
                }
            }
            let mut constructors = Vec::new();
            let mut seen = BTreeSet::new();
            for raw_constructor in &raw_eliminator.constructor {
                match QualifiedId::parse(&raw_constructor.entry) {
                    Ok(entry_ref) => {
                        if !seen.insert(entry_ref.to_string()) {
                            diagnostics.push(error(
                                path,
                                format!("duplicate eliminator constructor `{entry_ref}`"),
                            ));
                        }
                        if !is_lean_name(&raw_constructor.lean_name) {
                            diagnostics.push(error(
                                path,
                                format!("`{}` is not a Lean name", raw_constructor.lean_name),
                            ));
                        }
                        let mut binder_names = BTreeSet::new();
                        for name in raw_constructor
                            .fields
                            .iter()
                            .chain(&raw_constructor.induction_hypotheses)
                        {
                            if !lse::is_lse_identifier(name) || !binder_names.insert(name.clone()) {
                                diagnostics.push(error(
                                    path,
                                    format!("invalid or duplicate eliminator binder `{name}`"),
                                ));
                            }
                        }
                        constructors.push(EliminatorConstructor {
                            entry: entry_ref,
                            lean_name: raw_constructor.lean_name.clone(),
                            fields: raw_constructor.fields.clone(),
                            induction_hypotheses: raw_constructor.induction_hypotheses.clone(),
                        });
                    }
                    Err(parse_error) => diagnostics.push(error(path, parse_error)),
                }
            }
            if constructors.is_empty() {
                diagnostics.push(error(path, "an eliminator needs at least one constructor"));
            }
            Some(Eliminator {
                cases_lean_name: raw_eliminator.cases_lean_name.clone(),
                induction_lean_name: raw_eliminator.induction_lean_name.clone(),
                constructors,
            })
        }
        None => None,
    };

    if diagnostics.is_empty() {
        Ok(Entry {
            id: raw.id,
            category,
            frame,
            surface_arity: raw.surface_arity,
            signature,
            signature_canonical,
            signature_hash,
            universes,
            precedence,
            associativity,
            denotation,
            forms,
            render_math,
            render_text,
            calculation,
            eliminator,
        })
    } else {
        Err(diagnostics)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FORBIDDEN: [&str; 2] = ["\\def", "\\input"];

    fn ctx(is_core: bool, forbidden: &[String]) -> EntryContext<'_> {
        EntryContext {
            is_core,
            forbidden_controls: forbidden,
            max_scope_depth: 1024,
        }
    }

    fn atoms(surface: &str) -> Vec<Atom> {
        crate::source::scan::scan("<t>", surface, 1_000).expect("scans")
    }

    const PROBE: &str = r#"spec = "lexlean/entry/1"
id = "probe"
category = "term-constant"
signature = "(const lexlean.std.nat::nat)"
surface_arity = 0
frame = "atom"

[denotation]
kind = "lean"
module = "Init"
name = "Nat.zero"

[[form]]
id = "probe"
channel = "both"
surface = "probe"
canonical_source = true
features = []

[render]
math = "(operator-name probe)"
"#;

    fn forbidden() -> Vec<String> {
        FORBIDDEN.iter().map(|s| (*s).to_owned()).collect()
    }

    fn codes(result: Result<Entry, Vec<Diagnostic>>) -> Vec<String> {
        result
            .err()
            .unwrap_or_default()
            .iter()
            .map(|d| d.code.as_str().to_owned())
            .collect()
    }

    #[test]
    fn safety_predicate_by_channel() {
        assert!(surface_safety(&atoms("natural number"), Channel::Text).is_ok());
        assert!(surface_safety(&atoms("Euler's number"), Channel::Text).is_ok());
        assert!(surface_safety(&atoms("x1"), Channel::Text).is_err());
        assert!(surface_safety(&atoms("(x)"), Channel::Text).is_err());
        assert!(surface_safety(&atoms("ℕ"), Channel::Text).is_err());
        assert!(surface_safety(&atoms("ℕ"), Channel::Math).is_ok());
        assert!(surface_safety(&atoms("succ"), Channel::Math).is_ok());
        assert!(surface_safety(&atoms("+"), Channel::Math).is_ok());
        assert!(surface_safety(&atoms("f(x)"), Channel::Math).is_ok());
        assert!(surface_safety(&atoms("{x}"), Channel::Math).is_err());
        assert!(surface_safety(&atoms("x_1"), Channel::Math).is_err());
        assert!(surface_safety(&atoms("\"q\""), Channel::Math).is_err());
        assert!(surface_safety(&atoms("100"), Channel::Math).is_err());
        assert!(surface_safety(&atoms("x1"), Channel::Math).is_ok());
        assert!(surface_safety(&atoms("x1"), Channel::Both).is_err());
        assert!(surface_safety(&atoms("\\relax"), Channel::Math).is_err());
        assert!(surface_safety(&atoms("$"), Channel::Math).is_err());
        assert!(surface_safety(&atoms("%"), Channel::Math).is_err());
        // Combining and format scalars are never safe.
        assert!(surface_safety(&atoms("x\u{0301}"), Channel::Math).is_err());
        assert!(surface_safety(&atoms("a\u{200B}b"), Channel::Math).is_err());
        assert!(surface_safety(&atoms("\u{FEFF}"), Channel::Math).is_err());
        assert!(surface_safety(&atoms("z"), Channel::Both).is_ok());
        assert!(surface_safety(&atoms("z-x"), Channel::Both).is_ok());
        assert!(surface_safety(&atoms("z+x"), Channel::Both).is_err());
    }

    #[test]
    fn parses_the_minimal_entry() {
        let forbidden = forbidden();
        let entry = parse_entry("probe.toml", PROBE, &ctx(false, &forbidden)).expect("valid");
        assert_eq!(entry.id, "probe");
        assert_eq!(entry.category, Category::TermConstant);
        assert!(entry.render_math.is_some());
        assert!(entry.render_text.is_none());
    }

    #[test]
    fn surface_arity_follows_the_signature() {
        let forbidden = forbidden();
        let mismatched = PROBE.replace(
            "signature = \"(const lexlean.std.nat::nat)\"",
            "signature = \"(pi ((explicit n (const lexlean.std.nat::nat))) (const lexlean.std.nat::nat))\"",
        );
        assert_eq!(
            codes(parse_entry(
                "probe.toml",
                &mismatched,
                &ctx(false, &forbidden)
            )),
            vec!["LLR3004"]
        );
    }

    #[test]
    fn deep_lse_is_a_limit_failure() {
        let forbidden = forbidden();
        let deep = format!(
            "{}(const lexlean.std.nat::nat){}",
            "(app ".repeat(200_000),
            ")".repeat(200_000)
        );
        let text = PROBE.replace("(const lexlean.std.nat::nat)", &deep);
        let result = parse_entry("probe.toml", &text, &ctx(false, &forbidden));
        assert!(codes(result).contains(&"LLS8002".to_owned()));
        let deep_render = format!(
            "{}(space){}",
            "(group ".repeat(100_000),
            ")".repeat(100_000)
        );
        let text = PROBE.replace("(operator-name probe)", &deep_render);
        let result = parse_entry("probe.toml", &text, &ctx(false, &forbidden));
        assert!(codes(result).contains(&"LLS8002".to_owned()));
    }

    #[test]
    fn unsafe_canonical_and_alias_forms() {
        let forbidden = forbidden();
        let unsafe_canonical = PROBE.replace("surface = \"probe\"", "surface = \"pr{obe}\"");
        assert!(codes(parse_entry(
            "p.toml",
            &unsafe_canonical,
            &ctx(false, &forbidden)
        ))
        .contains(&"LLR3006".to_owned()));
        // A non-canonical alias is one control sequence (an input-only
        // spelling, §13.5 rule 3) or renderer-safe; a mixed raw-TeX alias is
        // rejected at load whether or not an LRE references it.
        let raw_alias = PROBE.replace(
            "[render]",
            "[[form]]\nid = \"alias\"\nchannel = \"math\"\nsurface = \"\\\\jobname{x} $ \\\\relax\"\ncanonical_source = false\nfeatures = []\n\n[render]",
        );
        assert_eq!(
            codes(parse_entry("p.toml", &raw_alias, &ctx(false, &forbidden))),
            vec!["LLR3006"]
        );
        let alias = PROBE.replace(
            "[render]",
            "[[form]]\nid = \"alias\"\nchannel = \"math\"\nsurface = \"\\\\probe\"\ncanonical_source = false\nfeatures = []\n\n[render]",
        );
        assert!(parse_entry("p.toml", &alias, &ctx(false, &forbidden)).is_ok());
        let injected = alias.replace("(operator-name probe)", "(self-form alias)");
        assert_eq!(
            codes(parse_entry("p.toml", &injected, &ctx(false, &forbidden))),
            vec!["LLR3006"]
        );
    }

    #[test]
    fn forbidden_controls_come_from_the_context() {
        let forbidden = forbidden();
        let text = PROBE.replace(
            "[render]",
            "[[form]]\nid = \"alias\"\nchannel = \"math\"\nsurface = \"\\\\def\"\ncanonical_source = false\nfeatures = []\n\n[render]",
        );
        assert_eq!(
            codes(parse_entry("p.toml", &text, &ctx(false, &forbidden))),
            vec!["LLR3004"]
        );
        assert!(parse_entry("p.toml", &text, &ctx(false, &[])).is_ok());
    }

    #[test]
    fn text_render_needs_a_text_category() {
        let forbidden = forbidden();
        let text = PROBE.replace(
            "math = \"(operator-name probe)\"",
            "math = \"(operator-name probe)\"\ntext = \"(self-form probe)\"",
        );
        assert!(parse_entry("p.toml", &text, &ctx(false, &forbidden)).is_ok());
        let math_only = text.replace(
            "category = \"term-constant\"",
            "category = \"predicate-constant\"",
        );
        assert!(
            codes(parse_entry("p.toml", &math_only, &ctx(false, &forbidden)))
                .contains(&"LLR3004".to_owned())
        );
    }

    #[test]
    fn eliminator_needs_a_sort_valued_signature() {
        let forbidden = forbidden();
        let text = format!(
            "{PROBE}\n[eliminator]\ncases_lean_name = \"Nat.casesOn\"\ninduction_lean_name = \"Nat.rec\"\n\n[[eliminator.constructor]]\nentry = \"lexlean.std.nat::zero\"\nlean_name = \"Nat.zero\"\nfields = []\ninduction_hypotheses = []\n"
        );
        assert!(codes(parse_entry("p.toml", &text, &ctx(false, &forbidden)))
            .contains(&"LLR3004".to_owned()));
        let typed = text
            .replace("category = \"term-constant\"", "category = \"type-noun\"")
            .replace(
                "signature = \"(const lexlean.std.nat::nat)\"",
                "signature = \"(sort (type 0))\"",
            )
            .replace("channel = \"both\"", "channel = \"text\"")
            .replace("[render]\nmath = \"(operator-name probe)\"\n", "");
        assert!(
            parse_entry("p.toml", &typed, &ctx(false, &forbidden)).is_ok(),
            "{typed}"
        );
    }

    #[test]
    fn lean_names_are_conservative() {
        assert!(is_lean_name("Nat.add_zero"));
        assert!(is_lean_name("_root_.x"));
        assert!(!is_lean_name("Nat..add"));
        assert!(!is_lean_name("«x»"));
        assert!(!is_lean_name("1x"));
        assert!(!is_lean_name(""));
    }
}
