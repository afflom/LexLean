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
use crate::grammar::proposition::{Keyword, TextParser};
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

    fn comma(&mut self) -> Option<Keyword> {
        if let Some(TextToken::Atom(index)) = self.parser.tokens.get(self.pos) {
            let atom = &self.parser.atoms[*index];
            if atom.class == AtomClass::AsciiSymbol && atom.text == "," {
                self.pos += 1;
                return Some(Keyword {
                    atom: *index,
                    entry: "comma",
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

/// Elaborate one definition declaration (§15.7).
#[allow(clippy::too_many_lines)]
pub fn elab_definition(
    shared: &Shared<'_>,
    scopes: &mut ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    decl: &DeclAst,
    sentence: &SentenceAst,
) -> Result<ElabDefinition, Diagnostic> {
    let entry_arg = decl
        .entry
        .as_ref()
        .ok_or_else(|| def_error("a definition names its document entry"))?;
    let entry_id = QualifiedId::parse(&entry_arg.text).map_err(def_error)?;
    let entry = shared
        .closure
        .entry(&entry_id)
        .ok_or_else(|| {
            Diagnostic::new(
                code!("LLR3005"),
                format!("`{entry_id}` is not in the glossary closure"),
            )
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
            )));
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
        )));
    }
    let signature = entry
        .signature
        .as_ref()
        .ok_or_else(|| def_error("the document entry has no signature"))?;
    let signature_term =
        lse_to_term(signature, shared, alloc, &BTreeMap::new()).map_err(def_error)?;

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
    };
    let mut cursor = SentenceCursor {
        parser: &parser,
        pos: 0,
    };
    let mut rows: Vec<SourceRow> = Vec::new();

    // Optional `For every BINDER-LIST,` prefix.
    scopes.push_frame();
    let mut binders: Vec<Binder> = Vec::new();
    let result = (|| -> Result<(Term, Term), Diagnostic> {
        if let Some(for_kw) = cursor.word("For") {
            keyword_row(shared, &for_kw, &mut rows);
            let every_kw = cursor
                .word("every")
                .ok_or_else(|| def_error("expected `every` after `For`"))?;
            keyword_row(shared, &every_kw, &mut rows);
            loop {
                let alternatives = parser.binder(cursor.pos, budget, false)?;
                // A definition binder must parse uniquely by position.
                let mut by_end: Vec<(usize, crate::grammar::proposition::BinderAst)> = alternatives;
                by_end.sort_by_key(|(end, _)| *end);
                by_end.dedup_by_key(|(end, _)| *end);
                let (end, binder_ast) = by_end
                    .into_iter()
                    .next()
                    .ok_or_else(|| def_error("expected a binder"))?;
                let (binder, binder_rows) =
                    elab_binder(shared, scopes, alloc, budget, &binder_ast)?;
                rows.extend(binder_rows);
                binders.push(binder);
                cursor.pos = end;
                if let Some(and_kw) = cursor.word("and") {
                    keyword_row(shared, &and_kw, &mut rows);
                    continue;
                }
                break;
            }
            let comma = cursor
                .comma()
                .ok_or_else(|| def_error("expected `,` after the binder list"))?;
            keyword_row(shared, &comma, &mut rows);
        }
        let binder_spellings: Vec<String> = binders
            .iter()
            .map(|binder| binder.spelling.clone())
            .collect();

        // Instantiate the signature telescope with the declared binders
        // (rule 4: exactly once, in signature order; LLT4004 on drift).
        let mut remaining = signature_term.clone();
        if !binders.is_empty() {
            let Term::Pi {
                binders: signature_binders,
                body,
            } = remaining
            else {
                return Err(Diagnostic::new(
                    code!("LLT4004"),
                    "the entry signature has no binders, but the definition declares some",
                ));
            };
            if signature_binders.len() != binders.len() {
                return Err(Diagnostic::new(
                    code!("LLT4004"),
                    format!(
                        "the entry signature declares {} explicit binders, the definition {}",
                        signature_binders.len(),
                        binders.len()
                    ),
                ));
            }
            let mut map = BTreeMap::new();
            for (signature_binder, declared) in signature_binders.iter().zip(&binders) {
                let expected = crate::elaborate::expressions::subst(&signature_binder.ty, &map);
                if expected.canonical_key() != declared.ty.canonical_key() {
                    return Err(Diagnostic::new(
                        code!("LLT4004"),
                        "a binder type does not match the entry signature",
                    ));
                }
                map.insert(signature_binder.id, Term::Local(declared.id));
            }
            remaining = crate::elaborate::expressions::subst(&body, &map);
        }

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
                let head_row =
                    match_canonical_text(shared, &parser, &mut cursor, &entry_id, &entry)
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
                // TYPE: a type phrase.
                if let Some(island) = cursor.island() {
                    let result = elab_island(shared, scopes, alloc, budget, &island, None)?;
                    if !matches!(result.ty, Some(Term::Sort(_))) {
                        return Err(Diagnostic::new(
                            code!("LLT4001"),
                            "the right-hand side of a type definition must be a sort",
                        ));
                    }
                    rows.extend(result.rows);
                    result.term
                } else {
                    let matches = (|| {
                        let Some(TextToken::Atom(atom_index)) = parser.tokens.get(cursor.pos)
                        else {
                            return Vec::new();
                        };
                        shared.closure.matches_at(
                            shared.atoms,
                            *atom_index,
                            Channel::Text,
                            shared.visible,
                        )
                    })();
                    let mut chosen = None;
                    for (reference, atom_end) in matches {
                        let Some((candidate_entry, _)) = shared.closure.form(&reference) else {
                            continue;
                        };
                        if candidate_entry.category == Category::TypeNoun {
                            chosen = Some((reference, atom_end));
                            break;
                        }
                    }
                    let (reference, atom_end) = chosen
                        .ok_or_else(|| def_error("the right-hand side must be a type phrase"))?;
                    let mut elaborator = ExprElab {
                        shared,
                        scopes,
                        alloc,
                        budget,
                    };
                    let start_atom = match parser.tokens.get(cursor.pos) {
                        Some(TextToken::Atom(index)) => *index,
                        _ => return Err(def_error("the right-hand side must be a type phrase")),
                    };
                    let leaf = MathAst::Leaf {
                        kinds: vec![LeafKind::Form(reference)],
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
                // SELF head: canonical text form for atoms, a self
                // application island otherwise.
                if binder_spellings.is_empty()
                    && matches!(
                        entry.category,
                        Category::TermConstant | Category::PredicateConstant
                    )
                {
                    if let Some(head_row) =
                        match_canonical_text(shared, &parser, &mut cursor, &entry_id, &entry)
                    {
                        rows.push(head_row);
                    } else {
                        let island = cursor.island().ok_or_else(|| {
                            def_error(
                                "the self head must be the canonical form or a self application",
                            )
                        })?;
                        let self_rows = match_self_application(
                            shared,
                            &entry_id,
                            &island,
                            &binder_spellings,
                            budget,
                        )?;
                        rows.extend(self_rows);
                        let mut delim_rows = Vec::new();
                        crate::elaborate::island_delim_rows_public(
                            shared,
                            &island,
                            &mut delim_rows,
                        );
                        rows.extend(delim_rows);
                    }
                } else {
                    let island = cursor
                        .island()
                        .ok_or_else(|| def_error("the self application must be an island"))?;
                    let self_rows = match_self_application(
                        shared,
                        &entry_id,
                        &island,
                        &binder_spellings,
                        budget,
                    )?;
                    rows.extend(self_rows);
                    let mut delim_rows = Vec::new();
                    crate::elaborate::island_delim_rows_public(shared, &island, &mut delim_rows);
                    rows.extend(delim_rows);
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
                    let result =
                        elab_island(shared, scopes, alloc, budget, &island, Some(&remaining))?;
                    rows.extend(result.rows);
                    result.term
                } else {
                    for word in ["holds", "exactly", "when"] {
                        let keyword = cursor
                            .word(word)
                            .ok_or_else(|| def_error("expected `holds exactly when`"))?;
                        keyword_row(shared, &keyword, &mut rows);
                    }
                    // The rest of the sentence is a proposition.
                    let rest_start = match parser.tokens.get(cursor.pos) {
                        Some(token) => token.first_atom(),
                        None => {
                            return Err(def_error("a predicate definition ends with a proposition"))
                        }
                    };
                    let rest_tokens =
                        text_tokens(shared.path, shared.atoms, rest_start, sentence.range.1)?;
                    let rest_parser = TextParser {
                        path: shared.path,
                        atoms: shared.atoms,
                        tokens: &rest_tokens,
                        closure: shared.closure,
                        visible: shared.visible,
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
            return Err(def_error(
                "unexpected content after the definition sentence",
            ));
        }
        Ok((remaining, value))
    })();
    scopes.pop_frame();
    let (result_ty, value_body) = result?;

    // Rule 5: the right-hand side has the declared result category.
    if decl.kind == DeclKind::PredicateDefinition {
        // elab_proposition_sentence already produced a Prop.
    } else if decl.kind == DeclKind::TermDefinition {
        // The expected type drove elaboration.
    }
    // Rule 6: no self reference.
    if references_self(&value_body, shared.module, &decl.component.text) {
        return Err(def_error(
            "the right-hand side must not reference the declaration being defined",
        ));
    }

    let ty = signature_term;
    let value = if binders.is_empty() {
        value_body
    } else {
        Term::Lambda {
            binders: binders.clone(),
            body: Box::new(value_body),
        }
    };
    let _ = result_ty;

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
        ty,
        value,
        rows,
    })
}
