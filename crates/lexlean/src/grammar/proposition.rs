//! The controlled proposition, binder, and phrase grammars (SPEC.md §15.3,
//! §15.4, §15.6). Recursive descent that returns every surviving parse
//! alternative; conservative elaboration collapses or rejects them (§14.4).

use std::collections::BTreeSet;

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::grammar::chart::{Budget, TextToken};
use crate::grammar::structural::AtomRange;
use crate::lexicon::entry::{Category, Channel};
use crate::lexicon::resolve::{Closure, FormRef};
use crate::source::atom::{Atom, AtomClass};
use crate::source::scan::compose_identifier;

/// A grammar keyword occurrence: the atom index and the core entry that
/// covers it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Keyword {
    /// The atom index.
    pub atom: usize,
    /// The covering core grammar entry's local ID.
    pub entry: &'static str,
}

/// A text binder (§15.4): a type-phrase and one fresh math local.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinderAst {
    /// The type phrase.
    pub type_phrase: TypePhraseAst,
    /// The fresh identifier spelling.
    pub spelling: String,
    /// The island carrying the identifier.
    pub island: TextToken,
    /// The identifier's atom range inside the island.
    pub ident_atoms: AtomRange,
    /// Keywords consumed by this binder (articles), for coverage.
    pub keywords: Vec<Keyword>,
}

/// A type phrase (§15.3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypePhraseAst {
    /// One linked type-noun frame.
    Noun {
        /// The type-noun candidates.
        candidates: Vec<FormRef>,
        /// The covered atom range.
        atoms: AtomRange,
    },
    /// One math island whose result is a sort.
    Math(TextToken),
}

/// One term phrase in the text channel (§15.3, §13.4): a mathematical
/// island, or a noun-of / binary-noun-of frame `the SELF of ARG [and ARG]`
/// whose arguments are themselves term phrases.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermPhraseAst {
    /// One mathematical island.
    Island(TextToken),
    /// `the SELF of ARG_0` or `the SELF of ARG_0 and ARG_1`.
    NounOf {
        /// The noun-function candidates sharing this surface.
        candidates: Vec<FormRef>,
        /// The SELF surface atoms.
        surface_atoms: AtomRange,
        /// The arguments, in slot order.
        args: Vec<TermPhraseAst>,
        /// The frame keywords (`the`, `of`, `and`), for coverage.
        keywords: Vec<Keyword>,
    },
}

impl TermPhraseAst {
    /// The first atom of the phrase, for spans.
    #[must_use]
    pub fn first_atom(&self) -> usize {
        match self {
            Self::Island(token) => token.first_atom(),
            Self::NounOf { keywords, .. } => keywords.first().map_or(0, |keyword| keyword.atom),
        }
    }
}

/// Whether a binder slot takes an article (§15.6): `there exists a x` requires
/// one; every other binder position forbids one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArticleRule {
    /// No article is accepted.
    Forbidden,
    /// Exactly one article (`a` or `an`) is required.
    Required,
}

/// One proposition parse (§15.6).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropAst {
    /// `if P, then Q`.
    Conditional {
        /// Antecedent.
        antecedent: Box<PropAst>,
        /// Consequent.
        consequent: Box<PropAst>,
        /// The keywords, for coverage.
        keywords: Vec<Keyword>,
    },
    /// `P if and only if Q`.
    Iff {
        /// Left side.
        left: Box<PropAst>,
        /// Right side.
        right: Box<PropAst>,
        /// The keywords.
        keywords: Vec<Keyword>,
    },
    /// `P implies Q`.
    Implies {
        /// Left side.
        left: Box<PropAst>,
        /// Right side.
        right: Box<PropAst>,
        /// The keyword.
        keywords: Vec<Keyword>,
    },
    /// `P or Q or ...`, left-folded.
    Or {
        /// The disjuncts, at least two.
        items: Vec<PropAst>,
        /// The keywords.
        keywords: Vec<Keyword>,
    },
    /// `P and Q and ...`, left-folded.
    And {
        /// The conjuncts, at least two.
        items: Vec<PropAst>,
        /// The keywords.
        keywords: Vec<Keyword>,
    },
    /// `not P`.
    Not {
        /// The negated proposition.
        inner: Box<PropAst>,
        /// The keyword.
        keywords: Vec<Keyword>,
    },
    /// `For every b and b', P`.
    ForAll {
        /// The binders, at least one.
        binders: Vec<BinderAst>,
        /// The body.
        body: Box<PropAst>,
        /// The keywords.
        keywords: Vec<Keyword>,
    },
    /// `there exists [exactly one] b such that P`.
    Exists {
        /// The one binder.
        binder: Box<BinderAst>,
        /// Unique existence?
        unique: bool,
        /// The body.
        body: Box<PropAst>,
        /// The keywords.
        keywords: Vec<Keyword>,
    },
    /// A math island whose linked result must be `Prop`.
    Math(TextToken),
    /// A fixed predicate frame (§13.4) applied to term-phrase arguments.
    Predicate {
        /// The predicate entry candidates.
        candidates: Vec<FormRef>,
        /// The predicate surface atoms.
        surface_atoms: AtomRange,
        /// The argument term phrases, in slot order.
        args: Vec<TermPhraseAst>,
        /// Frame keywords (`is`), for coverage.
        keywords: Vec<Keyword>,
    },
}

/// The word-to-core-entry map for grammar keywords. The words are literal
/// core entries (§12.3); coverage binds each occurrence to its entry.
#[must_use]
pub fn keyword_entry(word: &str) -> Option<&'static str> {
    Some(match word {
        "a" | "A" => "a",
        "an" | "An" => "an",
        "and" => "and",
        "as" => "as",
        "defined" => "defined",
        "every" => "every",
        "exactly" => "exactly",
        "exists" => "exists",
        "for" | "For" => "for",
        "holds" => "holds",
        "if" | "If" => "if",
        "implies" => "implies",
        "is" => "is",
        "not" | "Not" => "not",
        "one" => "one",
        "only" => "only",
        "or" => "or",
        "such" => "such",
        "that" => "that",
        "the" | "The" => "the",
        "then" => "then",
        "there" | "There" => "there",
        "when" => "when",
        "of" => "of",
        _ => return None,
    })
}

/// The alternatives at one grammar position.
type Alts<T> = Vec<(usize, T)>;

/// The shared context of one text-channel parse.
pub struct TextParser<'a> {
    /// The source display path.
    pub path: &'a str,
    /// The scanned atoms.
    pub atoms: &'a [Atom],
    /// The token view.
    pub tokens: &'a [TextToken],
    /// The glossary closure.
    pub closure: &'a Closure,
    /// The packages visible to this module.
    pub visible: &'a BTreeSet<String>,
    /// Does token 0 begin a sentence? Sentence-case keyword spellings
    /// (`If`, `Not`, `There`, `For`) are accepted only at token 0 of a
    /// sentence (§15.6); a proposition embedded after `holds exactly when`
    /// is not sentence-initial.
    pub sentence_initial: bool,
}

impl<'a> TextParser<'a> {
    /// The exact unknown-atom diagnosis (I1, §12.2): a text atom that no
    /// glossary form, grammar keyword, or proof keyword can ever cover is
    /// reported as `LLL1004` at its own span, in preference to a generic
    /// no-parse failure.
    pub fn unknown_atom_diagnostic(
        &self,
        budget: &mut Budget,
    ) -> Result<Option<Diagnostic>, Diagnostic> {
        let atom_indices: Vec<usize> = self
            .tokens
            .iter()
            .filter_map(|token| match token {
                TextToken::Atom(index) => Some(*index),
                TextToken::Island { .. } => None,
            })
            .collect();
        let Some(range_start) = atom_indices.first().copied() else {
            return Ok(None);
        };
        for index in &atom_indices {
            let atom = &self.atoms[*index];
            match atom.class {
                AtomClass::Whitespace => continue,
                AtomClass::Word
                    if (keyword_entry(atom.text.as_str()).is_some()
                        || crate::grammar::proof::proof_keyword_entry(atom.text.as_str())
                            .is_some()) =>
                {
                    continue;
                }
                _ => {}
            }
            let mut covered = false;
            for start in range_start..=*index {
                let edges = budget.edges_at(
                    self.closure,
                    self.atoms,
                    self.visible,
                    start,
                    Channel::Text,
                )?;
                if edges
                    .iter()
                    .any(|(_, end)| start <= *index && *index < *end)
                {
                    covered = true;
                    break;
                }
            }
            if !covered {
                return Ok(Some(
                    Diagnostic::new(
                        code!("LLL1004"),
                        format!(
                            "`{}` is not a declared atom in any visible glossary",
                            atom.text
                        ),
                    )
                    .with_span(atom.span(self.path)),
                ));
            }
        }
        Ok(None)
    }

    fn word_at(&self, pos: usize) -> Option<(&'a str, usize)> {
        match self.tokens.get(pos)? {
            TextToken::Atom(index) => {
                let atom = &self.atoms[*index];
                if atom.class == AtomClass::Word {
                    Some((atom.text.as_str(), *index))
                } else {
                    None
                }
            }
            TextToken::Island { .. } => None,
        }
    }

    fn is_word(&self, pos: usize, word: &str) -> Option<Keyword> {
        let (text, atom) = self.word_at(pos)?;
        if text == word {
            keyword_entry(word).map(|entry| Keyword { atom, entry })
        } else {
            None
        }
    }

    /// A keyword that may open a sentence: the lower-case spelling
    /// anywhere, or its sentence-case form exactly at token 0 of a
    /// sentence (§15.6).
    fn is_initial_word(&self, pos: usize, word: &str) -> Option<Keyword> {
        let (text, atom) = self.word_at(pos)?;
        let mut capitalized = String::new();
        let mut chars = word.chars();
        if let Some(first) = chars.next() {
            capitalized.extend(first.to_uppercase());
            capitalized.push_str(chars.as_str());
        }
        if text == word || (pos == 0 && self.sentence_initial && text == capitalized) {
            keyword_entry(word).map(|entry| Keyword { atom, entry })
        } else {
            None
        }
    }

    fn island_at(&self, pos: usize) -> Option<TextToken> {
        match self.tokens.get(pos)? {
            token @ TextToken::Island { .. } => Some(token.clone()),
            TextToken::Atom(_) => None,
        }
    }

    /// The token position whose first atom is `atom_end` or later.
    fn token_pos_after_atom(&self, from: usize, atom_end: usize) -> usize {
        let mut pos = from;
        while pos < self.tokens.len() && self.tokens[pos].first_atom() < atom_end {
            pos += 1;
        }
        pos
    }

    /// Glossary form matches starting at token `pos`, filtered by category.
    fn form_matches(
        &self,
        pos: usize,
        budget: &mut Budget,
        filter: impl Fn(Category) -> bool,
    ) -> Result<Vec<(FormRef, usize)>, Diagnostic> {
        let Some(TextToken::Atom(atom_index)) = self.tokens.get(pos) else {
            return Ok(Vec::new());
        };
        let mut out = Vec::new();
        for (reference, atom_end) in budget.edges_at(
            self.closure,
            self.atoms,
            self.visible,
            *atom_index,
            Channel::Text,
        )? {
            let Some((entry, _)) = self.closure.form(&reference) else {
                continue;
            };
            if filter(entry.category) {
                let token_end = self.token_pos_after_atom(pos, atom_end);
                out.push((reference, token_end));
            }
        }
        Ok(out)
    }

    /// One binder: type-phrase then a fresh-identifier island (§15.4).
    /// `article` says whether a leading article keyword is required or
    /// forbidden.
    pub fn binder(
        &self,
        pos: usize,
        budget: &mut Budget,
        article: ArticleRule,
    ) -> Result<Alts<BinderAst>, Diagnostic> {
        budget.state()?;
        let mut alternatives = Vec::new();
        let mut starts: Vec<(usize, Vec<Keyword>)> = Vec::new();
        match article {
            ArticleRule::Forbidden => starts.push((pos, Vec::new())),
            ArticleRule::Required => {
                for word in ["a", "an"] {
                    if let Some(keyword) = self.is_word(pos, word) {
                        starts.push((pos + 1, vec![keyword]));
                    }
                }
            }
        }
        for (start, keywords) in starts {
            // Type-noun phrase. Inflection is explicit lexicon data (§13.5):
            // a binder slot takes a singular, mid-sentence form, so plural
            // and sentence-case forms never match here.
            for (reference, after_noun) in
                self.form_matches(start, budget, |category| category == Category::TypeNoun)?
            {
                if let Some((_, form)) = self.closure.form(&reference) {
                    if form
                        .features
                        .iter()
                        .any(|feature| feature == "plural" || feature == "sentence-case")
                    {
                        continue;
                    }
                }
                if let Some(binder) = self.binder_local(
                    after_noun,
                    TypePhraseAst::Noun {
                        candidates: vec![reference],
                        atoms: self.token_atom_range(start, after_noun),
                    },
                ) {
                    let mut with_keywords = binder;
                    with_keywords.0 += 0;
                    let (end, mut ast) = with_keywords;
                    ast.keywords.splice(0..0, keywords.iter().cloned());
                    alternatives.push((end, ast));
                }
            }
            // Math type phrase.
            if let Some(island) = self.island_at(start) {
                if let Some((end, mut ast)) =
                    self.binder_local(start + 1, TypePhraseAst::Math(island))
                {
                    ast.keywords.splice(0..0, keywords.iter().cloned());
                    alternatives.push((end, ast));
                }
            }
        }
        Ok(alternatives)
    }

    fn token_atom_range(&self, start: usize, end: usize) -> AtomRange {
        let first = self.tokens[start].first_atom();
        let last = self.tokens[end.saturating_sub(1).max(start)].last_atom();
        (first, last + 1)
    }

    fn binder_local(&self, pos: usize, type_phrase: TypePhraseAst) -> Option<(usize, BinderAst)> {
        let island = self.island_at(pos)?;
        let TextToken::Island {
            inner_start,
            inner_end,
            ..
        } = island
        else {
            return None;
        };
        // Exactly one fresh ASCII identifier (§15.4).
        let mut index = inner_start;
        while index < inner_end && self.atoms[index].class == AtomClass::Whitespace {
            index += 1;
        }
        let (spelling, ident_end) = compose_identifier(self.atoms, index)?;
        let mut rest = ident_end;
        while rest < inner_end && self.atoms[rest].class == AtomClass::Whitespace {
            rest += 1;
        }
        if rest != inner_end {
            return None;
        }
        Some((
            pos + 1,
            BinderAst {
                type_phrase,
                spelling,
                island: island.clone(),
                ident_atoms: (index, ident_end),
                keywords: Vec::new(),
            },
        ))
    }

    /// The depth diagnostic for grammatical proposition nesting (§25.5).
    fn depth_check(&self, budget: &Budget, depth: u64, pos: usize) -> Result<(), Diagnostic> {
        budget
            .depth(depth, "parse (proposition nesting)")
            .map_err(|diagnostic| match self.tokens.get(pos) {
                Some(token) => diagnostic.with_span(self.atoms[token.first_atom()].span(self.path)),
                None => diagnostic,
            })
    }

    /// One proposition; `depth` counts nested connectives and quantifier
    /// bodies against `max_scope_depth` (§25.5).
    fn proposition(
        &self,
        pos: usize,
        budget: &mut Budget,
        depth: u64,
    ) -> Result<Alts<PropAst>, Diagnostic> {
        budget.state()?;
        self.depth_check(budget, depth, pos)?;
        let nested = depth.saturating_add(1);
        let mut alternatives = Vec::new();
        // conditional = "if" proposition "," "then" proposition
        if let Some(if_kw) = self.is_initial_word(pos, "if") {
            for (after_p, antecedent) in self.proposition(pos + 1, budget, nested)? {
                let Some(TextToken::Atom(comma_index)) = self.tokens.get(after_p) else {
                    continue;
                };
                if self.atoms[*comma_index].text != "," {
                    continue;
                }
                let Some(then_kw) = self.is_word(after_p + 1, "then") else {
                    continue;
                };
                let comma_kw = Keyword {
                    atom: *comma_index,
                    entry: "comma",
                };
                for (after_q, consequent) in self.proposition(after_p + 2, budget, nested)? {
                    budget.state()?;
                    alternatives.push((
                        after_q,
                        PropAst::Conditional {
                            antecedent: Box::new(antecedent.clone()),
                            consequent: Box::new(consequent),
                            keywords: vec![if_kw.clone(), comma_kw.clone(), then_kw.clone()],
                        },
                    ));
                }
            }
        }
        alternatives.extend(self.equivalence(pos, budget, depth)?);
        Ok(alternatives)
    }

    fn equivalence(
        &self,
        pos: usize,
        budget: &mut Budget,
        depth: u64,
    ) -> Result<Alts<PropAst>, Diagnostic> {
        let mut alternatives = Vec::new();
        for (after_left, left) in self.implication(pos, budget, depth)? {
            // Optional "if and only if".
            if let (Some(k1), Some(k2), Some(k3), Some(k4)) = (
                self.is_word(after_left, "if"),
                self.is_word(after_left + 1, "and"),
                self.is_word(after_left + 2, "only"),
                self.is_word(after_left + 3, "if"),
            ) {
                for (after_right, right) in
                    self.implication(after_left + 4, budget, depth.saturating_add(1))?
                {
                    budget.state()?;
                    alternatives.push((
                        after_right,
                        PropAst::Iff {
                            left: Box::new(left.clone()),
                            right: Box::new(right),
                            keywords: vec![k1.clone(), k2.clone(), k3.clone(), k4.clone()],
                        },
                    ));
                }
            }
            alternatives.push((after_left, left));
        }
        Ok(alternatives)
    }

    fn implication(
        &self,
        pos: usize,
        budget: &mut Budget,
        depth: u64,
    ) -> Result<Alts<PropAst>, Diagnostic> {
        self.depth_check(budget, depth, pos)?;
        let mut alternatives = Vec::new();
        for (after_left, left) in self.disjunction(pos, budget, depth)? {
            if let Some(keyword) = self.is_word(after_left, "implies") {
                for (after_right, right) in
                    self.implication(after_left + 1, budget, depth.saturating_add(1))?
                {
                    budget.state()?;
                    alternatives.push((
                        after_right,
                        PropAst::Implies {
                            left: Box::new(left.clone()),
                            right: Box::new(right),
                            keywords: vec![keyword.clone()],
                        },
                    ));
                }
            }
            alternatives.push((after_left, left));
        }
        Ok(alternatives)
    }

    fn disjunction(
        &self,
        pos: usize,
        budget: &mut Budget,
        depth: u64,
    ) -> Result<Alts<PropAst>, Diagnostic> {
        self.chain(
            pos,
            budget,
            depth,
            "or",
            Self::conjunction,
            |items, keywords| PropAst::Or { items, keywords },
        )
    }

    fn conjunction(
        &self,
        pos: usize,
        budget: &mut Budget,
        depth: u64,
    ) -> Result<Alts<PropAst>, Diagnostic> {
        self.chain(
            pos,
            budget,
            depth,
            "and",
            Self::negation,
            |items, keywords| PropAst::And { items, keywords },
        )
    }

    fn chain(
        &self,
        pos: usize,
        budget: &mut Budget,
        depth: u64,
        word: &str,
        next: impl Fn(&Self, usize, &mut Budget, u64) -> Result<Alts<PropAst>, Diagnostic> + Copy,
        build: impl Fn(Vec<PropAst>, Vec<Keyword>) -> PropAst + Copy,
    ) -> Result<Alts<PropAst>, Diagnostic> {
        let mut alternatives = Vec::new();
        // Every chain length is a live alternative; the sentence boundary
        // kills the wrong ones and the elaborator collapses the rest.
        let mut frontier: Alts<(Vec<PropAst>, Vec<Keyword>)> = next(self, pos, budget, depth)?
            .into_iter()
            .map(|(end, item)| (end, (vec![item], Vec::new())))
            .collect();
        while !frontier.is_empty() {
            let mut grown = Vec::new();
            for (end, (items, keywords)) in &frontier {
                if items.len() == 1 {
                    alternatives.push((*end, items[0].clone()));
                } else {
                    alternatives.push((*end, build(items.clone(), keywords.clone())));
                }
                if let Some(keyword) = self.is_word(*end, word) {
                    for (next_end, item) in next(self, *end + 1, budget, depth)? {
                        budget.state()?;
                        let mut new_items = items.clone();
                        new_items.push(item);
                        let mut new_keywords = keywords.clone();
                        new_keywords.push(keyword.clone());
                        grown.push((next_end, (new_items, new_keywords)));
                    }
                }
            }
            frontier = grown;
        }
        Ok(alternatives)
    }

    #[allow(clippy::too_many_lines)]
    fn negation(
        &self,
        pos: usize,
        budget: &mut Budget,
        depth: u64,
    ) -> Result<Alts<PropAst>, Diagnostic> {
        budget.state()?;
        self.depth_check(budget, depth, pos)?;
        let nested = depth.saturating_add(1);
        let mut alternatives = Vec::new();
        if let Some(keyword) = self.is_initial_word(pos, "not") {
            for (end, inner) in self.negation(pos + 1, budget, nested)? {
                alternatives.push((
                    end,
                    PropAst::Not {
                        inner: Box::new(inner),
                        keywords: vec![keyword.clone()],
                    },
                ));
            }
        }
        // quantified: For/for every binder { and binder } , proposition
        if let (Some(for_kw), Some(every_kw)) = (
            self.is_initial_word(pos, "for"),
            self.is_word(pos + 1, "every"),
        ) {
            let mut binder_frontier: Alts<(Vec<BinderAst>, Vec<Keyword>)> = self
                .binder(pos + 2, budget, ArticleRule::Forbidden)?
                .into_iter()
                .map(|(end, binder)| (end, (vec![binder], Vec::new())))
                .collect();
            while !binder_frontier.is_empty() {
                let mut grown = Vec::new();
                for (end, (binders, and_keywords)) in &binder_frontier {
                    // Try to close the binder list with a comma and a body.
                    if let Some(TextToken::Atom(comma_index)) = self.tokens.get(*end) {
                        if self.atoms[*comma_index].text == "," {
                            let comma_kw = Keyword {
                                atom: *comma_index,
                                entry: "comma",
                            };
                            for (body_end, body) in self.proposition(*end + 1, budget, nested)? {
                                budget.state()?;
                                let mut keywords =
                                    vec![for_kw.clone(), every_kw.clone(), comma_kw.clone()];
                                keywords.extend(and_keywords.iter().cloned());
                                alternatives.push((
                                    body_end,
                                    PropAst::ForAll {
                                        binders: binders.clone(),
                                        body: Box::new(body),
                                        keywords,
                                    },
                                ));
                            }
                        }
                    }
                    if let Some(and_kw) = self.is_word(*end, "and") {
                        for (next_end, binder) in
                            self.binder(*end + 1, budget, ArticleRule::Forbidden)?
                        {
                            let mut new_binders = binders.clone();
                            new_binders.push(binder);
                            let mut new_keywords = and_keywords.clone();
                            new_keywords.push(and_kw.clone());
                            grown.push((next_end, (new_binders, new_keywords)));
                        }
                    }
                }
                binder_frontier = grown;
            }
        }
        // there exists [exactly one | article] binder such that proposition
        if let Some(there_kw) = self.is_initial_word(pos, "there") {
            if let Some(exists_kw) = self.is_word(pos + 1, "exists") {
                let mut heads: Vec<(usize, bool, Vec<Keyword>)> = Vec::new();
                if let (Some(exactly_kw), Some(one_kw)) = (
                    self.is_word(pos + 2, "exactly"),
                    self.is_word(pos + 3, "one"),
                ) {
                    heads.push((
                        pos + 4,
                        true,
                        vec![there_kw.clone(), exists_kw.clone(), exactly_kw, one_kw],
                    ));
                }
                heads.push((pos + 2, false, vec![there_kw.clone(), exists_kw.clone()]));
                for (binder_pos, unique, head_keywords) in heads {
                    // §15.6: `there exists article binder`; the article is
                    // required, and `exactly one` takes none.
                    let article = if unique {
                        ArticleRule::Forbidden
                    } else {
                        ArticleRule::Required
                    };
                    for (after_binder, binder) in self.binder(binder_pos, budget, article)? {
                        let (Some(such_kw), Some(that_kw)) = (
                            self.is_word(after_binder, "such"),
                            self.is_word(after_binder + 1, "that"),
                        ) else {
                            continue;
                        };
                        for (body_end, body) in
                            self.proposition(after_binder + 2, budget, nested)?
                        {
                            budget.state()?;
                            let mut keywords = head_keywords.clone();
                            keywords.push(such_kw.clone());
                            keywords.push(that_kw.clone());
                            alternatives.push((
                                body_end,
                                PropAst::Exists {
                                    binder: Box::new(binder.clone()),
                                    unique,
                                    body: Box::new(body),
                                    keywords,
                                },
                            ));
                        }
                    }
                }
            }
        }
        // atomic: math island
        if let Some(island) = self.island_at(pos) {
            alternatives.push((pos + 1, PropAst::Math(island)));
        }
        // atomic: predicate frames over term-phrase arguments
        alternatives.extend(self.predicate_frame(pos, budget, nested)?);
        Ok(alternatives)
    }

    /// One term phrase (§15.3, §13.4): a mathematical island, or the
    /// noun-of / binary-noun-of frame `the SELF of ARG [and ARG]` whose
    /// arguments are term phrases. Every alternative is returned; the
    /// enclosing grammar and conservative elaboration select (§14.4).
    pub fn term_phrase(
        &self,
        pos: usize,
        budget: &mut Budget,
        depth: u64,
    ) -> Result<Alts<TermPhraseAst>, Diagnostic> {
        budget.state()?;
        self.depth_check(budget, depth, pos)?;
        let nested = depth.saturating_add(1);
        let mut alternatives = Vec::new();
        if let Some(island) = self.island_at(pos) {
            alternatives.push((pos + 1, TermPhraseAst::Island(island)));
        }
        let Some(the_kw) = self.is_word(pos, "the") else {
            return Ok(alternatives);
        };
        for (reference, after_noun) in self.form_matches(pos + 1, budget, |category| {
            matches!(
                category,
                Category::NounFunction | Category::BinaryNounFunction
            )
        })? {
            let Some((entry, _)) = self.closure.form(&reference) else {
                continue;
            };
            let Some(of_kw) = self.is_word(after_noun, "of") else {
                continue;
            };
            let surface_atoms = self.token_atom_range(pos + 1, after_noun);
            for (after_first, first) in self.term_phrase(after_noun + 1, budget, nested)? {
                if entry.category == Category::NounFunction {
                    alternatives.push((
                        after_first,
                        TermPhraseAst::NounOf {
                            candidates: vec![reference.clone()],
                            surface_atoms,
                            args: vec![first],
                            keywords: vec![the_kw.clone(), of_kw.clone()],
                        },
                    ));
                    continue;
                }
                let Some(and_kw) = self.is_word(after_first, "and") else {
                    continue;
                };
                for (after_second, second) in self.term_phrase(after_first + 1, budget, nested)? {
                    budget.state()?;
                    alternatives.push((
                        after_second,
                        TermPhraseAst::NounOf {
                            candidates: vec![reference.clone()],
                            surface_atoms,
                            args: vec![first.clone(), second],
                            keywords: vec![the_kw.clone(), of_kw.clone(), and_kw.clone()],
                        },
                    ));
                }
            }
        }
        Ok(alternatives)
    }

    fn predicate_frame(
        &self,
        pos: usize,
        budget: &mut Budget,
        depth: u64,
    ) -> Result<Alts<PropAst>, Diagnostic> {
        let mut alternatives = Vec::new();
        for (after_first, first_arg) in self.term_phrase(pos, budget, depth)? {
            // adjective: ARG is SELF
            if let Some(is_kw) = self.is_word(after_first, "is") {
                for (reference, end) in self.form_matches(after_first + 1, budget, |category| {
                    category == Category::AdjectivePredicate
                })? {
                    alternatives.push((
                        end,
                        PropAst::Predicate {
                            surface_atoms: self.token_atom_range(after_first + 1, end),
                            candidates: vec![reference],
                            args: vec![first_arg.clone()],
                            keywords: vec![is_kw.clone()],
                        },
                    ));
                }
            }
            // intransitive: ARG SELF ; transitive: ARG SELF ARG
            for (reference, end) in self.form_matches(after_first, budget, |category| {
                matches!(
                    category,
                    Category::IntransitivePredicate | Category::TransitivePredicate
                )
            })? {
                let Some((entry, _)) = self.closure.form(&reference) else {
                    continue;
                };
                if entry.category == Category::IntransitivePredicate {
                    alternatives.push((
                        end,
                        PropAst::Predicate {
                            surface_atoms: self.token_atom_range(after_first, end),
                            candidates: vec![reference],
                            args: vec![first_arg.clone()],
                            keywords: Vec::new(),
                        },
                    ));
                    continue;
                }
                for (after_second, second_arg) in self.term_phrase(end, budget, depth)? {
                    budget.state()?;
                    alternatives.push((
                        after_second,
                        PropAst::Predicate {
                            surface_atoms: self.token_atom_range(after_first, end),
                            candidates: vec![reference.clone()],
                            args: vec![first_arg.clone(), second_arg],
                            keywords: Vec::new(),
                        },
                    ));
                }
            }
        }
        Ok(alternatives)
    }

    /// Every full-consumption proposition parse of the token range.
    pub fn proposition_sentence(&self, budget: &mut Budget) -> Result<Vec<PropAst>, Diagnostic> {
        let alternatives = self.proposition(0, budget, 1)?;
        let complete: Vec<PropAst> = alternatives
            .into_iter()
            .filter(|(end, _)| *end == self.tokens.len())
            .map(|(_, ast)| ast)
            .collect();
        if complete.is_empty() {
            let span = match self.tokens.first() {
                Some(token) => {
                    let first = &self.atoms[token.first_atom()];
                    first.span(self.path)
                }
                None => crate::diagnostic::Span::whole_file(self.path),
            };
            if let Some(unknown) = self.unknown_atom_diagnostic(budget)? {
                return Err(unknown);
            }
            return Err(Diagnostic::new(
                code!("LLP2001"),
                "no parse under the controlled proposition grammar",
            )
            .with_span(span));
        }
        Ok(complete)
    }
}

/// One phrase item parse (§15.3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PhraseItemAst {
    /// A concept word: label-word, type-noun, or the nominal form of a term
    /// or function entry.
    Word {
        /// The candidates.
        candidates: Vec<FormRef>,
        /// The covered atoms.
        atoms: AtomRange,
    },
    /// A non-`Prop` math island.
    Math(TextToken),
    /// A noun-of term phrase, `the SELF of ARG [and ARG]` (§15.3: the
    /// canonical nominal form of a function entry with its arguments).
    TermPhrase(TermPhraseAst),
    /// Core phrase punctuation `:`, `-`, `(`, `)`.
    Punctuation {
        /// The atom index.
        atom: usize,
        /// The core entry ID covering it.
        entry: &'static str,
    },
}

/// Parse a title or heading phrase (§15.3): nonempty, no proposition
/// machinery, no predicate frames, no proof instructions.
///
/// Segmentation is a lattice, not a greedy walk (§14.1): every extent a
/// glossary form covers at a position is an alternative, and the returned
/// parses are the complete covers --- the paths that reach the end of the
/// phrase covering every token exactly once. A path that dead-ends because
/// nothing covers what follows is simply not a cover, and the caller
/// decides between the covers that remain by linking them (§14.4). Every
/// path step is charged against `max_parse_states` (§25.5).
pub fn parse_phrase(
    parser: &TextParser<'_>,
    budget: &mut Budget,
) -> Result<Vec<Vec<PhraseItemAst>>, Diagnostic> {
    if parser.tokens.is_empty() {
        return Err(Diagnostic::new(
            code!("LLP2001"),
            "a phrase is a nonempty sequence of concepts",
        )
        .with_span(crate::diagnostic::Span::whole_file(parser.path)));
    }
    let mut covers: Vec<Vec<PhraseItemAst>> = Vec::new();
    let mut failure: Option<Diagnostic> = None;
    let mut frontier: Vec<(usize, Vec<PhraseItemAst>)> = vec![(0, Vec::new())];
    while !frontier.is_empty() {
        let mut next_frontier: Vec<(usize, Vec<PhraseItemAst>)> = Vec::new();
        for (pos, items) in frontier {
            budget.state()?;
            if pos >= parser.tokens.len() {
                if !covers.contains(&items) {
                    covers.push(items);
                }
                continue;
            }
            let steps = match phrase_steps(parser, budget, pos)? {
                Ok(steps) => steps,
                Err(dead_end) => {
                    if failure.is_none() {
                        failure = Some(dead_end);
                    }
                    continue;
                }
            };
            for (item, end) in steps {
                let mut extended = items.clone();
                extended.push(item);
                next_frontier.push((end, extended));
            }
        }
        frontier = next_frontier;
    }
    if covers.is_empty() {
        return Err(failure.unwrap_or_else(|| {
            Diagnostic::new(
                code!("LLP2001"),
                "a phrase is a nonempty sequence of concepts",
            )
            .with_span(crate::diagnostic::Span::whole_file(parser.path))
        }));
    }
    Ok(covers)
}

/// The lattice steps out of one phrase position: each is one item and the
/// token position after it. `Err` is a dead end at this position --- the
/// diagnostic a phrase with no other cover reports --- and is distinct from
/// the outer `Err`, which is a parse failure of the phrase as a whole.
#[allow(clippy::type_complexity)]
fn phrase_steps(
    parser: &TextParser<'_>,
    budget: &mut Budget,
    pos: usize,
) -> Result<Result<Vec<(PhraseItemAst, usize)>, Diagnostic>, Diagnostic> {
    let atom_index = match &parser.tokens[pos] {
        token @ TextToken::Island { .. } => {
            return Ok(Ok(vec![(PhraseItemAst::Math(token.clone()), pos + 1)]));
        }
        TextToken::Atom(atom_index) => *atom_index,
    };
    let atom = &parser.atoms[atom_index];
    let punct = match (atom.class, atom.text.as_str()) {
        (AtomClass::AsciiSymbol, ":") => Some("colon"),
        (AtomClass::AsciiSymbol, "-") => Some("hyphen"),
        (AtomClass::Delimiter, "(") => Some("paren-open"),
        (AtomClass::Delimiter, ")") => Some("paren-close"),
        _ => None,
    };
    if let Some(entry) = punct {
        return Ok(Ok(vec![(
            PhraseItemAst::Punctuation {
                atom: atom_index,
                entry,
            },
            pos + 1,
        )]));
    }
    // `the SELF of ARG [and ARG]`: a noun-of term phrase. Each parse of it
    // is one lattice step; distinct extents are alternatives, not a guess.
    if atom.class == AtomClass::Word && atom.text == "the" {
        let noun_of: Vec<(PhraseItemAst, usize)> = parser
            .term_phrase(pos, budget, 1)?
            .into_iter()
            .filter(|(_, phrase)| matches!(phrase, TermPhraseAst::NounOf { .. }))
            .map(|(end, phrase)| (PhraseItemAst::TermPhrase(phrase), end))
            .collect();
        if !noun_of.is_empty() {
            return Ok(Ok(noun_of));
        }
    }
    let matches = parser.form_matches(pos, budget, |category| {
        matches!(
            category,
            Category::LabelWord
                | Category::TypeNoun
                | Category::TermConstant
                | Category::Function
                | Category::PrefixFunction
                | Category::PostfixFunction
                | Category::InfixFunction
                | Category::NounFunction
                | Category::BinaryNounFunction
        )
    })?;
    if matches.is_empty() {
        return Ok(Err(Diagnostic::new(
            code!("LLL1004"),
            format!("`{}` is not a phrase concept", atom.text),
        )
        .with_span(atom.span(parser.path))));
    }
    // One step per covered extent, each carrying the candidates that cover
    // it; extents are ordered so the shortest cover is tried first.
    let mut ends: Vec<usize> = matches.iter().map(|(_, end)| *end).collect();
    ends.sort_unstable();
    ends.dedup();
    Ok(Ok(ends
        .into_iter()
        .map(|end| {
            (
                PhraseItemAst::Word {
                    atoms: parser.token_atom_range(pos, end),
                    candidates: matches
                        .iter()
                        .filter(|(_, other)| *other == end)
                        .map(|(reference, _)| reference.clone())
                        .collect(),
                },
                end,
            )
        })
        .collect()))
}
