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
    #[must_use]
    pub const fn has_signature(self) -> bool {
        !matches!(self, Self::Structural | Self::Grammar | Self::LabelWord)
    }

    /// The channels in which a canonical source form is required (§13.5
    /// rule 7).
    #[must_use]
    pub fn required_channels(self) -> &'static [Channel] {
        match self {
            Self::Structural | Self::Grammar => &[],
            Self::LabelWord
            | Self::TypeNoun
            | Self::TermConstant
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

/// The §12.4 always-forbidden controls, shared with source scanning.
#[must_use]
pub fn forbidden_controls() -> &'static [&'static str] {
    &[
        "\\def",
        "\\gdef",
        "\\edef",
        "\\xdef",
        "\\let",
        "\\futurelet",
        "\\newcommand",
        "\\renewcommand",
        "\\providecommand",
        "\\input",
        "\\include",
        "\\usepackage",
        "\\documentclass",
        "\\csname",
        "\\catcode",
        "\\write",
        "\\read",
        "\\openin",
        "\\openout",
        "\\special",
        "\\immediate",
        "\\verbatim",
        "\\verb",
    ]
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

/// Parse and validate one entry file (§13.2–§13.7). `is_core` says whether
/// the containing package is `lexlean.core`.
#[allow(clippy::too_many_lines)]
pub fn parse_entry(path: &str, text: &str, is_core: bool) -> Result<Entry, Vec<Diagnostic>> {
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
        (Some(text), true) => match lse::parse(text) {
            Ok(parsed) => {
                if let Err(scope_error) = parsed.check_scopes(&universe_set) {
                    diagnostics.push(error(path, format!("invalid signature: {scope_error}")));
                }
                let canonical = parsed.print(true);
                signature_hash = Some(Sha256Digest::of(canonical.as_bytes()));
                signature_canonical = Some(canonical);
                signature = Some(parsed);
            }
            Err(parse_error) => {
                diagnostics.push(error(path, format!("invalid signature LSE: {parse_error}")));
            }
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
            (Some(value_text), 1) => match lse::parse(value_text) {
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
                Err(parse_error) => {
                    diagnostics.push(error(path, format!("invalid defined LSE: {parse_error}")));
                    Denotation::Defined {
                        value: Lse::SortProp,
                        text: String::new(),
                    }
                }
            },
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
        // A surface is parsed into primitive atoms at package-load time.
        let atoms = match crate::source::scan::scan("<form>", surface, 1024) {
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
                && forbidden_controls().contains(&atom.text.as_str())
            {
                diagnostics.push(error(
                    path,
                    format!(
                        "form `{}` declares the always-forbidden control `{}`",
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
        if raw_form.canonical_source && !is_core {
            let safe = atoms.iter().all(|atom| match atom.class {
                AtomClass::Word | AtomClass::Numeral => true,
                AtomClass::Whitespace => true,
                AtomClass::AsciiSymbol => {
                    if channel.covers(Channel::Text) {
                        matches!(atom.text.as_str(), ":" | "-")
                    } else {
                        !matches!(
                            atom.text.as_str(),
                            "\\" | "%" | "$" | "#" | "&" | "~" | "^" | "_"
                        )
                    }
                }
                AtomClass::Delimiter => {
                    !matches!(atom.text.as_str(), "{" | "}") || !channel.covers(Channel::Text)
                }
                AtomClass::UnicodeSymbol => channel.covers(Channel::Math),
                AtomClass::Control => false,
            });
            if !safe {
                diagnostics.push(
                    Diagnostic::new(
                        code!("LLR3006"),
                        format!(
                            "form `{}`: the canonical surface is not renderer-safe",
                            raw_form.id
                        ),
                    )
                    .with_span(crate::diagnostic::Span::whole_file(path)),
                );
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
    for channel in [Channel::Text, Channel::Math] {
        let canonical_count = forms
            .iter()
            .filter(|form| form.canonical_source && form.channel.covers(channel))
            .count();
        if canonical_count > 1 {
            diagnostics.push(error(
                path,
                format!(
                    "more than one canonical source form for the {} channel",
                    if channel == Channel::Text {
                        "text"
                    } else {
                        "math"
                    }
                ),
            ));
        }
        if category.required_channels().contains(&channel) && canonical_count == 0 {
            diagnostics.push(error(
                path,
                format!(
                    "category `{}` requires a canonical source form in the {} channel",
                    category.as_str(),
                    if channel == Channel::Text {
                        "text"
                    } else {
                        "math"
                    }
                ),
            ));
        }
    }

    // Renders (§13.9). A math frame with surface arguments requires a math
    // template; slot use is exact.
    let mut render_math = None;
    let mut render_text = None;
    if let Some(raw_render) = &raw.render {
        if matches!(category, Category::Structural | Category::Grammar) {
            diagnostics.push(error(
                path,
                "structural and grammar entries do not carry render templates",
            ));
        }
        for (channel_name, text_value, slot) in [
            ("math", &raw_render.math, &mut render_math),
            ("text", &raw_render.text, &mut render_text),
        ] {
            if let Some(render_source) = text_value {
                match lre::parse(render_source) {
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
                        for self_form in render.self_form_refs() {
                            if !forms.iter().any(|form| form.id == self_form) {
                                diagnostics.push(error(
                                    path,
                                    format!("render references unknown self form `{self_form}`"),
                                ));
                            }
                        }
                        *slot = Some(render);
                    }
                    Err(parse_error) => {
                        diagnostics.push(error(
                            path,
                            format!("invalid {channel_name} LRE: {parse_error}"),
                        ));
                    }
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

    // Eliminator descriptor (§16.11): only a type authorizes cases and
    // induction.
    let eliminator = match &raw.eliminator {
        Some(raw_eliminator) => {
            if category != Category::TypeNoun {
                diagnostics.push(error(
                    path,
                    "an eliminator descriptor belongs to a type-noun",
                ));
            }
            if !is_lean_name(&raw_eliminator.cases_lean_name)
                || !is_lean_name(&raw_eliminator.induction_lean_name)
            {
                diagnostics.push(error(path, "eliminator Lean names must be valid"));
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
