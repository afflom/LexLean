//! Definition sentences (SPEC.md §15.7): the exact type, term, and
//! predicate forms, with the self head, explicit arguments, and signature
//! order checked exactly (DF-05) and the built type compared canonically
//! against the document entry's signature (§17.7, LLT4004).

use std::collections::BTreeMap;

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::elaborate::expressions::{lse_to_term, ExprElab};
use crate::elaborate::resolve::{LocalAlloc, ScopeStack};
use crate::elaborate::{elab_binder, elab_island, elab_proposition_sentence, Shared};
use crate::grammar::chart::{text_tokens, Budget, TextToken};
use crate::grammar::math::{LeafKind, MathAst};
use crate::grammar::proposition::{ArticleRule, Keyword, TextParser};
use crate::grammar::structural::{DeclAst, SentenceAst};
use crate::ir::declaration::DeclKind;
use crate::ir::term::{Binder, GlobalRef, Term};
use crate::lexicon::entry::{Category, Channel, Entry};
use crate::lexicon::lse::QualifiedId;
use crate::source::atom::AtomClass;
use crate::source::coverage::{Origin, SourceRow};

/// The elaborated definition: the explicit type, the value, and coverage.
pub struct ElabDefinition {
    /// The document entry realized.
    pub entry: QualifiedId,
    /// The explicit generated type.
    pub ty: Term,
    /// The generated value.
    pub value: Term,
    /// Coverage rows.
    pub rows: Vec<SourceRow>,
}

fn def_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLF5001"), message)
}

fn keyword_row(shared: &Shared<'_>, keyword: &Keyword, rows: &mut Vec<SourceRow>) {
    let atom = &shared.atoms[keyword.atom];
    rows.push(SourceRow {
        path: shared.path.to_owned(),
        byte_start: atom.byte_start,
        byte_end: atom.byte_end,
        class: atom.class,
        binding: Origin::Structural {
            package: "lexlean.core".to_owned(),
            entry: keyword.entry.to_owned(),
        },
    });
}

/// Scan a value for a self reference (§15.7 rule 6).
fn references_self(term: &Term, module: &str, component: &str) -> bool {
    match term {
        Term::Global(GlobalRef::Document(reference), _) => {
            reference.module == module && reference.component == component
        }
        Term::Global(..) | Term::Local(_) | Term::Sort(_) => false,
        Term::App {
            function,
            explicit_args,
            ..
        } => {
            references_self(function, module, component)
                || explicit_args
                    .iter()
                    .any(|argument| references_self(argument, module, component))
        }
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            binders
                .iter()
                .any(|binder| references_self(&binder.ty, module, component))
                || references_self(body, module, component)
        }
        Term::Let {
            binder,
            value,
            body,
        } => {
            references_self(&binder.ty, module, component)
                || references_self(value, module, component)
                || references_self(body, module, component)
        }
        Term::NatLiteral { expected_type, .. } => references_self(expected_type, module, component),
    }
}

struct SentenceCursor<'a, 'b> {
    parser: &'b TextParser<'a>,
    pos: usize,
}

impl SentenceCursor<'_, '_> {
    fn word(&mut self, expected: &str) -> Option<Keyword> {
        if let Some(TextToken::Atom(index)) = self.parser.tokens.get(self.pos) {
            let atom = &self.parser.atoms[*index];
            if atom.class == AtomClass::Word && atom.text == expected {
                self.pos += 1;
                return crate::grammar::proposition::keyword_entry(expected).map(|entry| Keyword {
                    atom: *index,
                    entry,
                });
            }
        }
        None
    }

    fn island(&mut self) -> Option<TextToken> {
        if let Some(token @ TextToken::Island { .. }) = self.parser.tokens.get(self.pos) {
            self.pos += 1;
            return Some(token.clone());
        }
        None
    }
}

/// Match the entry's canonical text form at the cursor; returns its
/// coverage row.
fn match_canonical_text(
    shared: &Shared<'_>,
    parser: &TextParser<'_>,
    cursor: &mut SentenceCursor<'_, '_>,
    entry_id: &QualifiedId,
    entry: &Entry,
) -> Option<SourceRow> {
    let form = entry
        .forms
        .iter()
        .find(|form| form.canonical_source && form.channel.covers(Channel::Text))?;
    let Some(TextToken::Atom(start_atom)) = parser.tokens.get(cursor.pos) else {
        return None;
    };
    let mut source_at = *start_atom;
    for form_atom in &form.atoms {
        if form_atom.class == AtomClass::Whitespace {
            if shared.atoms.get(source_at)?.class != AtomClass::Whitespace {
                return None;
            }
            source_at += 1;
            continue;
        }
        let atom = shared.atoms.get(source_at)?;
        if atom.class != form_atom.class || atom.text != form_atom.text {
            return None;
        }
        source_at += 1;
    }
    let row = SourceRow {
        path: shared.path.to_owned(),
        byte_start: shared.atoms[*start_atom].byte_start,
        byte_end: shared.atoms[source_at - 1].byte_end,
        class: AtomClass::Word,
        binding: Origin::Form {
            package: entry_id.package.clone(),
            entry: entry_id.entry.clone(),
            form: form.id.clone(),
        },
    };
    while cursor.pos < parser.tokens.len() && parser.tokens[cursor.pos].first_atom() < source_at {
        cursor.pos += 1;
    }
    Some(row)
}

/// Match a self application island: the entry applied to exactly the binder
/// spellings, once each, in signature order (§15.7 rule 4).
fn match_self_application(
    shared: &Shared<'_>,
    entry_id: &QualifiedId,
    island: &TextToken,
    binder_spellings: &[String],
    budget: &mut Budget,
) -> Result<Vec<SourceRow>, Diagnostic> {
    let TextToken::Island {
        inner_start,
        inner_end,
        ..
    } = island
    else {
        return Err(def_error("the self head must be a mathematical island"));
    };
    let ast = crate::grammar::math::parse_math(
        shared.path,
        shared.atoms,
        (*inner_start, *inner_end),
        shared.closure,
        shared.visible,
        budget,
    )?;
    let mut rows = Vec::new();
    let head_matches = |kinds: &[LeafKind], rows: &mut Vec<SourceRow>, atoms: (usize, usize)| {
        let matched = kinds.iter().any(|kind| match kind {
            LeafKind::Form(reference) => {
                reference.package == entry_id.package && reference.entry == entry_id.entry
            }
            LeafKind::Ident(_) => false,
        });
        if matched {
            if let Some(LeafKind::Form(reference)) = kinds.iter().find(|kind| {
                matches!(kind, LeafKind::Form(reference)
                    if reference.package == entry_id.package && reference.entry == entry_id.entry)
            }) {
                rows.push(SourceRow {
                    path: shared.path.to_owned(),
                    byte_start: shared.atoms[atoms.0].byte_start,
                    byte_end: shared.atoms[atoms.1 - 1].byte_end,
                    class: shared.atoms[atoms.0].class,
                    binding: Origin::Form {
                        package: reference.package.clone(),
                        entry: reference.entry.clone(),
                        form: reference.form.clone(),
                    },
                });
            }
        }
        matched
    };
    let ident_arg = |ast: &MathAst, expected: &str, rows: &mut Vec<SourceRow>| -> bool {
        if let MathAst::Leaf { kinds, atoms } = ast {
            if kinds
                .iter()
                .any(|kind| matches!(kind, LeafKind::Ident(name) if name == expected))
            {
                rows.push(SourceRow {
                    path: shared.path.to_owned(),
                    byte_start: shared.atoms[atoms.0].byte_start,
                    byte_end: shared.atoms[atoms.1 - 1].byte_end,
                    class: AtomClass::Word,
                    binding: Origin::Metadata {
                        owner: format!("{entry_id}"),
                    },
                });
                return true;
            }
        }
        false
    };
    let ok = match &ast {
        MathAst::Call { head, args, .. } => {
            let MathAst::Leaf { kinds, atoms } = &**head else {
                return Err(def_error("the self head must name the declared entry"));
            };
            head_matches(kinds, &mut rows, *atoms)
                && args.len() == binder_spellings.len()
                && args
                    .iter()
                    .zip(binder_spellings)
                    .all(|(argument, spelling)| ident_arg(argument, spelling, &mut rows))
        }
        MathAst::Infix {
            candidates,
            op_atoms,
            lhs,
            rhs,
        } => {
            let matched = candidates.iter().any(|reference| {
                reference.package == entry_id.package && reference.entry == entry_id.entry
            });
            if matched {
                rows.push(SourceRow {
                    path: shared.path.to_owned(),
                    byte_start: shared.atoms[op_atoms.0].byte_start,
                    byte_end: shared.atoms[op_atoms.1 - 1].byte_end,
                    class: shared.atoms[op_atoms.0].class,
                    binding: Origin::Form {
                        package: entry_id.package.clone(),
                        entry: entry_id.entry.clone(),
                        form: candidates
                            .iter()
                            .find(|reference| {
                                reference.package == entry_id.package
                                    && reference.entry == entry_id.entry
                            })
                            .map(|reference| reference.form.clone())
                            .unwrap_or_default(),
                    },
                });
            }
            matched
                && binder_spellings.len() == 2
                && ident_arg(lhs, &binder_spellings[0], &mut rows)
                && ident_arg(rhs, &binder_spellings[1], &mut rows)
        }
        MathAst::Leaf { kinds, atoms } if binder_spellings.is_empty() => {
            head_matches(kinds, &mut rows, *atoms)
        }
        _ => false,
    };
    if !ok {
        return Err(def_error(
            "the self head must apply the declared entry to each explicit signature binder exactly once, in signature order",
        ));
    }
    // The remaining structural atoms of the self application --- parens and
    // argument commas --- are core structure (I1): every accepted atom has
    // exactly one origin.
    for index in *inner_start..*inner_end {
        let atom = &shared.atoms[index];
        if atom.class == AtomClass::Whitespace {
            continue;
        }
        if rows
            .iter()
            .any(|row| row.byte_start <= atom.byte_start && atom.byte_end <= row.byte_end)
        {
            continue;
        }
        let entry = match atom.text.as_str() {
            "(" => "paren-open",
            ")" => "paren-close",
            "," => "comma",
            _ => {
                return Err(def_error(format!(
                    "`{}` has no role in a self application",
                    atom.text
                )))
            }
        };
        rows.push(SourceRow {
            path: shared.path.to_owned(),
            byte_start: atom.byte_start,
            byte_end: atom.byte_end,
            class: atom.class,
            binding: Origin::Structural {
                package: "lexlean.core".to_owned(),
                entry: entry.to_owned(),
            },
        });
    }
    Ok(rows)
}

/// An argument island of a self head must contain exactly the expected
/// binder spelling (§15.7 rule 4); returns its coverage rows.
fn self_argument_island(
    shared: &Shared<'_>,
    entry_id: &QualifiedId,
    island: &TextToken,
    expected: &str,
) -> Option<Vec<SourceRow>> {
    let TextToken::Island {
        inner_start,
        inner_end,
        ..
    } = island
    else {
        return None;
    };
    let mut index = *inner_start;
    while index < *inner_end && shared.atoms[index].class == AtomClass::Whitespace {
        index += 1;
    }
    let (spelling, ident_end) = crate::source::scan::compose_identifier(shared.atoms, index)?;
    let mut rest = ident_end;
    while rest < *inner_end && shared.atoms[rest].class == AtomClass::Whitespace {
        rest += 1;
    }
    if rest != *inner_end || spelling != expected {
        return None;
    }
    let mut rows = vec![SourceRow {
        path: shared.path.to_owned(),
        byte_start: shared.atoms[index].byte_start,
        byte_end: shared.atoms[ident_end - 1].byte_end,
        class: AtomClass::Word,
        binding: Origin::Metadata {
            owner: format!("{entry_id}"),
        },
    }];
    crate::elaborate::island_delim_rows_public(shared, island, &mut rows);
    Some(rows)
}

/// The self head of a term or predicate definition with declared binders
/// (§15.7): a self-application island through the entry's math frame, the
/// noun-of frame `the SELF of ARG [and ARG]`, or a text predicate frame
/// `ARG is SELF`, `ARG SELF`, `ARG SELF ARG` (§13.4), each argument being
/// exactly the next declared binder in signature order.
fn match_self_head(
    shared: &Shared<'_>,
    parser: &TextParser<'_>,
    cursor: &mut SentenceCursor<'_, '_>,
    entry_id: &QualifiedId,
    entry: &Entry,
    binder_spellings: &[String],
    budget: &mut Budget,
) -> Result<Vec<SourceRow>, Diagnostic> {
    let frame_error = || {
        def_error(format!(
            "the self head must apply `{entry_id}` through its `{}` frame to each explicit signature binder exactly once, in signature order",
            entry.frame.as_str()
        ))
    };
    let mut rows = Vec::new();
    match entry.category {
        Category::NounFunction | Category::BinaryNounFunction => {
            let the_kw = cursor.word("the").ok_or_else(frame_error)?;
            keyword_row(shared, &the_kw, &mut rows);
            let head_row = match_canonical_text(shared, parser, cursor, entry_id, entry)
                .ok_or_else(frame_error)?;
            rows.push(head_row);
            let of_kw = cursor.word("of").ok_or_else(frame_error)?;
            keyword_row(shared, &of_kw, &mut rows);
            let arity = if entry.category == Category::NounFunction {
                1
            } else {
                2
            };
            if binder_spellings.len() != arity {
                return Err(frame_error());
            }
            for (index, spelling) in binder_spellings.iter().enumerate() {
                if index == 1 {
                    let and_kw = cursor.word("and").ok_or_else(frame_error)?;
                    keyword_row(shared, &and_kw, &mut rows);
                }
                let island = cursor.island().ok_or_else(frame_error)?;
                rows.extend(
                    self_argument_island(shared, entry_id, &island, spelling)
                        .ok_or_else(frame_error)?,
                );
            }
            Ok(rows)
        }
        Category::AdjectivePredicate
        | Category::IntransitivePredicate
        | Category::TransitivePredicate => {
            let arity = if entry.category == Category::TransitivePredicate {
                2
            } else {
                1
            };
            if binder_spellings.len() != arity {
                return Err(frame_error());
            }
            let first = cursor.island().ok_or_else(frame_error)?;
            rows.extend(
                self_argument_island(shared, entry_id, &first, &binder_spellings[0])
                    .ok_or_else(frame_error)?,
            );
            if entry.category == Category::AdjectivePredicate {
                let is_kw = cursor.word("is").ok_or_else(frame_error)?;
                keyword_row(shared, &is_kw, &mut rows);
            }
            let head_row = match_canonical_text(shared, parser, cursor, entry_id, entry)
                .ok_or_else(frame_error)?;
            rows.push(head_row);
            if entry.category == Category::TransitivePredicate {
                let second = cursor.island().ok_or_else(frame_error)?;
                rows.extend(
                    self_argument_island(shared, entry_id, &second, &binder_spellings[1])
                        .ok_or_else(frame_error)?,
                );
            }
            Ok(rows)
        }
        _ => {
            let island = cursor
                .island()
                .ok_or_else(|| def_error("the self application must be a mathematical island"))?;
            let mut self_rows =
                match_self_application(shared, entry_id, &island, binder_spellings, budget)?;
            crate::elaborate::island_delim_rows_public(shared, &island, &mut self_rows);
            Ok(self_rows)
        }
    }
}

/// One binder-list alternative of a definition prefix: the token position
/// after the closing comma, the binders, and the prefix keywords.
struct PrefixAlternative {
    after: usize,
    binders: Vec<crate::grammar::proposition::BinderAst>,
    keywords: Vec<Keyword>,
}

/// Every parse of `For every BINDER-LIST ,` at the sentence start (§15.4,
/// §15.7); the empty prefix when the sentence does not begin with `For`.
fn prefix_alternatives(
    parser: &TextParser<'_>,
    budget: &mut Budget,
) -> Result<Vec<PrefixAlternative>, Diagnostic> {
    let mut cursor = SentenceCursor { parser, pos: 0 };
    let Some(for_kw) = cursor.word("For") else {
        return Ok(vec![PrefixAlternative {
            after: 0,
            binders: Vec::new(),
            keywords: Vec::new(),
        }]);
    };
    let every_kw = cursor
        .word("every")
        .ok_or_else(|| def_error("expected `every` after `For`"))?;
    let mut alternatives = Vec::new();
    let mut frontier: Vec<PrefixAlternative> = vec![PrefixAlternative {
        after: cursor.pos,
        binders: Vec::new(),
        keywords: vec![for_kw, every_kw],
    }];
    while !frontier.is_empty() {
        let mut grown = Vec::new();
        for state in &frontier {
            for (end, binder) in parser.binder(state.after, budget, ArticleRule::Forbidden)? {
                budget.state()?;
                let Some(TextToken::Atom(index)) = parser.tokens.get(end) else {
                    continue;
                };
                let atom = &parser.atoms[*index];
                if atom.class != AtomClass::AsciiSymbol {
                    continue;
                }
                let mut binders = state.binders.clone();
                binders.push(binder);
                let mut keywords = state.keywords.clone();
                match atom.text.as_str() {
                    ";" => {
                        keywords.push(Keyword {
                            atom: *index,
                            entry: "semicolon",
                        });
                        grown.push(PrefixAlternative {
                            after: end + 1,
                            binders,
                            keywords,
                        });
                    }
                    "," => {
                        keywords.push(Keyword {
                            atom: *index,
                            entry: "comma",
                        });
                        alternatives.push(PrefixAlternative {
                            after: end + 1,
                            binders,
                            keywords,
                        });
                    }
                    _ => {}
                }
            }
        }
        frontier = grown;
    }
    if alternatives.is_empty() {
        return Err(def_error(
            "expected a `;`-separated binder list closed by `,` after `For every`",
        ));
    }
    Ok(alternatives)
}

/// The elaboration of one definition-sentence alternative.
struct BodyResult {
    ty: Term,
    value: Term,
    rows: Vec<SourceRow>,
}

/// The context one definition alternative elaborates in.
struct DefinitionContext<'c, 'a> {
    shared: &'c Shared<'a>,
    decl: &'c DeclAst,
    entry_id: &'c QualifiedId,
    entry: &'c Entry,
    signature_term: &'c Term,
    parser: &'c TextParser<'a>,
}

/// Elaborate one binder-list alternative of a definition sentence to its
/// type and value (§15.7). The caller owns the scope frame.
#[allow(clippy::too_many_lines)]
fn elab_definition_alternative(
    context: &DefinitionContext<'_, '_>,
    scopes: &mut ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    prefix: &PrefixAlternative,
) -> Result<BodyResult, Diagnostic> {
    let shared = context.shared;
    let decl = context.decl;
    let entry_id = context.entry_id;
    let entry = context.entry;
    let parser = context.parser;
    let mut rows: Vec<SourceRow> = Vec::new();
    for keyword in &prefix.keywords {
        keyword_row(shared, keyword, &mut rows);
    }
    let mut binders: Vec<Binder> = Vec::new();
    for binder_ast in &prefix.binders {
        let (binder, binder_rows) = elab_binder(shared, scopes, alloc, budget, binder_ast)?;
        rows.extend(binder_rows);
        binders.push(binder);
    }
    let binder_spellings: Vec<String> = binders
        .iter()
        .map(|binder| binder.spelling.clone())
        .collect();
    let mut cursor = SentenceCursor {
        parser,
        pos: prefix.after,
    };

    // Rule 4: exactly the signature's explicit binders, once each, in
    // signature order --- with or without a `For every` prefix.
    let (signature_binders, signature_body) =
        crate::elaborate::expressions::flatten_pi(context.signature_term);
    let explicit_count = signature_binders
        .iter()
        .filter(|binder| binder.mode == crate::lexicon::lse::BinderMode::Explicit)
        .count();
    if explicit_count != binders.len() {
        return Err(Diagnostic::new(
            code!("LLT4004"),
            format!(
                "the entry signature of `{entry_id}` declares {explicit_count} explicit binders, the definition declares {}",
                binders.len()
            ),
        ));
    }
    // The declared binders align with the signature's explicit binders in
    // order; an implicit or instance binder of the signature has no
    // sentence counterpart and becomes a like-moded binder of the value.
    let mut map = BTreeMap::new();
    let mut value_binders: Vec<Binder> = Vec::new();
    let mut declared_iter = binders.iter();
    for signature_binder in &signature_binders {
        let expected = crate::elaborate::expressions::subst(&signature_binder.ty, &map);
        match signature_binder.mode {
            crate::lexicon::lse::BinderMode::Explicit => {
                let Some(declared) = declared_iter.next() else {
                    return Err(Diagnostic::new(
                        code!("LLI9001"),
                        "phase definitions: explicit binder count checked above",
                    ));
                };
                if expected.eq_key() != declared.ty.eq_key() {
                    return Err(Diagnostic::new(
                        code!("LLT4004"),
                        format!(
                            "the type of binder `{}` does not match the entry signature of `{entry_id}`",
                            declared.spelling
                        ),
                    ));
                }
                map.insert(signature_binder.id, Term::Local(declared.id));
                value_binders.push(declared.clone());
            }
            crate::lexicon::lse::BinderMode::Implicit
            | crate::lexicon::lse::BinderMode::Instance => {
                let id = alloc.fresh();
                map.insert(signature_binder.id, Term::Local(id));
                value_binders.push(Binder {
                    id,
                    mode: signature_binder.mode,
                    ty: expected,
                    spelling: signature_binder.spelling.clone(),
                });
            }
        }
    }
    let remaining = crate::elaborate::expressions::subst(&signature_body, &map);

    // The self head and the definition keywords, by kind.
    let value = match decl.kind {
        DeclKind::TypeDefinition => {
            let article = cursor
                .word("A")
                .or_else(|| cursor.word("An"))
                .or_else(|| cursor.word("a"))
                .or_else(|| cursor.word("an"))
                .ok_or_else(|| def_error("a type definition begins with `A` or `An`"))?;
            keyword_row(shared, &article, &mut rows);
            let head_row = match_canonical_text(shared, parser, &mut cursor, entry_id, entry)
                .ok_or_else(|| {
                    def_error("the self head must be the entry's canonical text form")
                })?;
            rows.push(head_row);
            for word in ["is", "defined", "as"] {
                let keyword = cursor
                    .word(word)
                    .ok_or_else(|| def_error("expected `is defined as`"))?;
                keyword_row(shared, &keyword, &mut rows);
            }
            // TYPE: a type phrase (§15.3): a math island whose result is a
            // sort, or one type-noun frame; every candidate is elaborated
            // and exactly one distinct linked type must survive (§14.4).
            if let Some(island) = cursor.island() {
                let result = elab_island(shared, scopes, alloc, budget, &island, None)?;
                // The island's type must be a sort, read through defined
                // type nouns (`type` defined as `(sort (type 0))`, §13.6).
                let island_ty = result.ty.as_ref().map(|ty| {
                    crate::elaborate::delta::unfold(ty, shared, alloc, budget.max_depth())
                });
                if !matches!(island_ty, Some(Term::Sort(_))) {
                    return Err(Diagnostic::new(
                        code!("LLT4001"),
                        "the right-hand side of a type definition must be a sort",
                    )
                    .with_span(shared.atoms[island.first_atom()].span(shared.path)));
                }
                rows.extend(result.rows);
                result.term
            } else {
                let Some(TextToken::Atom(start_atom)) = parser.tokens.get(cursor.pos) else {
                    return Err(def_error("the right-hand side must be a type phrase"));
                };
                let start_atom = *start_atom;
                let matches: Vec<(crate::lexicon::resolve::FormRef, usize)> = budget
                    .edges_at(
                        shared.closure,
                        shared.atoms,
                        shared.visible,
                        start_atom,
                        Channel::Text,
                    )?
                    .into_iter()
                    .filter(|(reference, _)| {
                        shared
                            .closure
                            .form(reference)
                            .is_some_and(|(candidate, _)| candidate.category == Category::TypeNoun)
                    })
                    .collect();
                let Some((_, atom_end)) = matches.first() else {
                    return Err(def_error("the right-hand side must be a type phrase"));
                };
                let atom_end = *atom_end;
                if matches.iter().any(|(_, other)| *other != atom_end) {
                    return Err(Diagnostic::new(
                        code!("LLP2002"),
                        "ambiguous lexical segmentation of the type phrase",
                    )
                    .with_span(shared.atoms[start_atom].span(shared.path)));
                }
                let mut elaborator = ExprElab::new(shared, scopes, alloc, budget);
                let leaf = MathAst::Leaf {
                    kinds: matches
                        .into_iter()
                        .map(|(reference, _)| LeafKind::Form(reference))
                        .collect(),
                    atoms: (start_atom, atom_end),
                };
                let result = elaborator.elaborate(&leaf, None)?;
                rows.extend(result.rows.clone());
                while cursor.pos < parser.tokens.len()
                    && parser.tokens[cursor.pos].first_atom() < atom_end
                {
                    cursor.pos += 1;
                }
                result.term
            }
        }
        DeclKind::TermDefinition | DeclKind::PredicateDefinition => {
            // SELF head: the canonical text form for a constant, otherwise
            // the self application through the entry's frame (§15.7).
            if binder_spellings.is_empty()
                && matches!(
                    entry.category,
                    Category::TermConstant | Category::PredicateConstant
                )
            {
                if let Some(head_row) =
                    match_canonical_text(shared, parser, &mut cursor, entry_id, entry)
                {
                    rows.push(head_row);
                } else {
                    let island = cursor.island().ok_or_else(|| {
                        def_error("the self head must be the canonical form or a self application")
                    })?;
                    let mut self_rows = match_self_application(
                        shared,
                        entry_id,
                        &island,
                        &binder_spellings,
                        budget,
                    )?;
                    crate::elaborate::island_delim_rows_public(shared, &island, &mut self_rows);
                    rows.extend(self_rows);
                }
            } else {
                rows.extend(match_self_head(
                    shared,
                    parser,
                    &mut cursor,
                    entry_id,
                    entry,
                    &binder_spellings,
                    budget,
                )?);
            }
            if decl.kind == DeclKind::TermDefinition {
                for word in ["is", "defined", "as"] {
                    let keyword = cursor
                        .word(word)
                        .ok_or_else(|| def_error("expected `is defined as`"))?;
                    keyword_row(shared, &keyword, &mut rows);
                }
                let island = cursor
                    .island()
                    .ok_or_else(|| def_error("the right-hand side must be a term"))?;
                let result = elab_island(shared, scopes, alloc, budget, &island, Some(&remaining))?;
                rows.extend(result.rows);
                result.term
            } else {
                for word in ["holds", "exactly", "when"] {
                    let keyword = cursor
                        .word(word)
                        .ok_or_else(|| def_error("expected `holds exactly when`"))?;
                    keyword_row(shared, &keyword, &mut rows);
                }
                // The rest of the sentence is a proposition, not
                // sentence-initial (§15.6).
                let Some(rest_token) = parser.tokens.get(cursor.pos) else {
                    return Err(def_error("a predicate definition ends with a proposition"));
                };
                let rest_start = rest_token.first_atom();
                let sentence_end = parser
                    .tokens
                    .last()
                    .map_or(rest_start, |token| token.last_atom() + 1);
                let rest_tokens = text_tokens(shared.path, shared.atoms, rest_start, sentence_end)?;
                let rest_parser = TextParser {
                    path: shared.path,
                    atoms: shared.atoms,
                    tokens: &rest_tokens,
                    closure: shared.closure,
                    visible: shared.visible,
                    sentence_initial: false,
                };
                let alternatives = rest_parser.proposition_sentence(budget)?;
                cursor.pos = parser.tokens.len();
                let (term, prop_rows) =
                    elab_proposition_sentence(shared, scopes, alloc, budget, &alternatives)?;
                rows.extend(prop_rows);
                term
            }
        }
        _ => {
            return Err(Diagnostic::new(
                code!("LLI9001"),
                "phase definitions: theorem-like kind in the definition elaborator",
            ));
        }
    };

    if cursor.pos != parser.tokens.len() {
        let atom = &shared.atoms[parser.tokens[cursor.pos].first_atom()];
        return Err(
            def_error("unexpected content after the definition sentence")
                .with_span(atom.span(shared.path)),
        );
    }
    let value = if value_binders.is_empty() {
        value
    } else {
        Term::Lambda {
            binders: value_binders,
            body: Box::new(value),
        }
    };
    Ok(BodyResult {
        ty: context.signature_term.clone(),
        value,
        rows,
    })
}

/// Elaborate one definition declaration (§15.7). Every binder-list
/// alternative and every right-hand-side alternative is elaborated;
/// semantically identical results collapse and exactly one distinct
/// linked definition must remain (§14.4).
#[allow(clippy::too_many_lines)]
pub fn elab_definition(
    shared: &Shared<'_>,
    scopes: &mut ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    decl: &DeclAst,
    sentence: &SentenceAst,
) -> Result<ElabDefinition, Diagnostic> {
    let sentence_span = {
        let first = &shared.atoms[sentence.range.0];
        let last = &shared.atoms[sentence.period];
        crate::diagnostic::Span {
            path: shared.path.to_owned(),
            byte_start: first.byte_start,
            byte_end: last.byte_end,
            line_start: first.line_start,
            column_start: first.column_start,
            line_end: last.line_end,
            column_end: last.column_end,
        }
    };
    let entry_arg = decl
        .entry
        .as_ref()
        .ok_or_else(|| def_error("a definition names its document entry"))?;
    let entry_span = {
        let first = &shared.atoms[entry_arg.range.0.min(shared.atoms.len() - 1)];
        first.span(shared.path)
    };
    let entry_id = QualifiedId::parse(&entry_arg.text)
        .map_err(|reason| def_error(reason).with_span(entry_span.clone()))?;
    let entry = shared
        .closure
        .entry(&entry_id)
        .ok_or_else(|| {
            Diagnostic::new(
                code!("LLR3005"),
                format!("`{entry_id}` is not in the glossary closure"),
            )
            .with_span(entry_span.clone())
        })?
        .clone();
    // Rule 2: the denotation is `document` and names this module and
    // component.
    match &entry.denotation {
        crate::lexicon::entry::Denotation::Document { module, component }
            if module == shared.module && *component == decl.component.text => {}
        _ => {
            return Err(def_error(format!(
                "`{entry_id}` must have a document denotation naming {}::{}",
                shared.module, decl.component.text
            ))
            .with_span(entry_span));
        }
    }
    // Rule 3: the signature agrees with the declaration kind.
    let category_ok = match decl.kind {
        DeclKind::TypeDefinition => entry.category == Category::TypeNoun,
        DeclKind::TermDefinition => matches!(
            entry.category,
            Category::TermConstant
                | Category::Function
                | Category::PrefixFunction
                | Category::PostfixFunction
                | Category::InfixFunction
                | Category::NounFunction
                | Category::BinaryNounFunction
        ),
        DeclKind::PredicateDefinition => matches!(
            entry.category,
            Category::PredicateConstant
                | Category::AdjectivePredicate
                | Category::IntransitivePredicate
                | Category::TransitivePredicate
                | Category::InfixPredicate
        ),
        _ => false,
    };
    if !category_ok {
        return Err(def_error(format!(
            "entry category `{}` does not agree with a {}",
            entry.category.as_str(),
            decl.kind.as_str()
        ))
        .with_span(entry_span));
    }
    let signature = entry.signature.as_ref().ok_or_else(|| {
        def_error("the document entry has no signature").with_span(entry_span.clone())
    })?;
    let signature_term =
        lse_to_term(signature, shared, alloc, &BTreeMap::new(), None).map_err(|failure| {
            failure
                .diagnostic(code!("LLF5001"))
                .with_span(entry_span.clone())
        })?;

    let tokens = text_tokens(
        shared.path,
        shared.atoms,
        sentence.range.0,
        sentence.range.1,
    )?;
    let parser = TextParser {
        path: shared.path,
        atoms: shared.atoms,
        tokens: &tokens,
        closure: shared.closure,
        visible: shared.visible,
        sentence_initial: true,
    };
    let context = DefinitionContext {
        shared,
        decl,
        entry_id: &entry_id,
        entry: &entry,
        signature_term: &signature_term,
        parser: &parser,
    };
    let prefixes = prefix_alternatives(&parser, budget)
        .map_err(|diagnostic| with_default_span(diagnostic, &sentence_span))?;
    let mut survivors: Vec<(String, BodyResult)> = Vec::new();
    let mut first_failure: Option<Diagnostic> = None;
    for prefix in &prefixes {
        scopes.push_frame();
        let result = elab_definition_alternative(&context, scopes, alloc, budget, prefix);
        scopes.pop_frame();
        match result {
            Ok(body) => {
                let key = format!("{}\n{}", body.ty.eq_key(), body.value.eq_key());
                if !survivors.iter().any(|(existing, _)| *existing == key) {
                    survivors.push((key, body));
                }
            }
            Err(diagnostic) => {
                if first_failure.is_none() {
                    first_failure = Some(diagnostic);
                }
            }
        }
    }
    let body = match survivors.len() {
        1 => survivors.into_iter().next().expect("one").1,
        0 => {
            // Rule 6 (§15.7): a right-hand side that names the declaration
            // being defined cannot resolve it (the declaration exists only
            // after its definition), so the resolution failure that names
            // this very component is the recursion diagnostic.
            let self_reference = format!(
                "document declaration `{}::{}` is not available here",
                shared.module, decl.component.text
            );
            let failure = match first_failure {
                Some(diagnostic) if diagnostic.message.contains(&self_reference) => def_error(
                    "the right-hand side must not reference the declaration being defined",
                )
                .with_span(
                    diagnostic
                        .primary
                        .clone()
                        .unwrap_or_else(|| sentence_span.clone()),
                ),
                Some(diagnostic) => diagnostic,
                None => def_error("no definition interpretation survives"),
            };
            return Err(with_default_span(failure, &sentence_span));
        }
        _ => {
            return Err(crate::elaborate::ambiguity_diagnostic(
                survivors.iter().map(|(_, body)| &body.value),
            )
            .with_span(sentence_span));
        }
    };

    // Rule 6: no self reference.
    if references_self(&body.value, shared.module, &decl.component.text) {
        return Err(def_error(
            "the right-hand side must not reference the declaration being defined",
        )
        .with_span(sentence_span));
    }
    let mut rows = body.rows;
    // The sentence period.
    let period = &shared.atoms[sentence.period];
    rows.push(SourceRow {
        path: shared.path.to_owned(),
        byte_start: period.byte_start,
        byte_end: period.byte_end,
        class: period.class,
        binding: Origin::Structural {
            package: "lexlean.core".to_owned(),
            entry: "period".to_owned(),
        },
    });

    Ok(ElabDefinition {
        entry: entry_id,
        ty: body.ty,
        value: body.value,
        rows,
    })
}

/// Give a diagnostic the definition sentence's span when it carries none
/// (§20.1).
fn with_default_span(diagnostic: Diagnostic, span: &crate::diagnostic::Span) -> Diagnostic {
    if diagnostic.primary.is_some() {
        diagnostic
    } else {
        diagnostic.with_span(span.clone())
    }
}
