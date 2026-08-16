//! Canonical source formatting (SPEC.md §23.5): NFC, LF, two spaces per
//! section nesting level, sorted imports, safe canonical forms, one
//! sentence per line, one final LF. Formatting preserves linked IR; the
//! formatter compares pre- and post-render canonical IR and fails if they
//! differ.

use std::collections::BTreeMap;

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::ir::declaration::{AxiomPolicy, DeclBody, DeclKind, Declaration};
use crate::ir::document::{Block, DocumentModule, Phrase, PhraseItem, Section};
use crate::ir::proof::{Proof, RewriteTarget};
use crate::ir::term::{Binder, CoreRef, GlobalRef, LocalId, Term};
use crate::lexicon::entry::{Associativity, Channel, Entry};
use crate::lexicon::lse::QualifiedId;
use crate::lexicon::resolve::Closure;
use crate::link::CheckedModule;

struct Fmt<'a> {
    closure: &'a Closure,
    spellings: BTreeMap<LocalId, String>,
    out: String,
}

fn fmt_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLB6002"), message)
}

impl Fmt<'_> {
    fn entry_for_global(&self, global: &GlobalRef) -> Option<(QualifiedId, &Entry)> {
        let qualified = match global {
            GlobalRef::Core(core) => QualifiedId {
                package: "lexlean.core".to_owned(),
                entry: match core {
                    CoreRef::Eq => "eq",
                    CoreRef::And => "land",
                    CoreRef::Or => "lor",
                    CoreRef::Not => "lnot",
                    CoreRef::Iff => "iff",
                    CoreRef::Exists | CoreRef::ExistsUnique => return None,
                }
                .to_owned(),
            },
            GlobalRef::External(external) => QualifiedId::parse(&external.entry).ok()?,
            GlobalRef::DefinedLexicon(defined) => QualifiedId::parse(&defined.entry).ok()?,
            GlobalRef::Document(_) => return None,
        };
        let entry = self.closure.entry(&qualified)?;
        Some((qualified, entry))
    }

    fn spelling(&self, id: LocalId) -> String {
        self.spellings
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("x{}", id.0))
    }

    fn term_prec(&self, term: &Term) -> u8 {
        match term {
            Term::App { function, .. } => match &**function {
                Term::Global(global, _) => self
                    .entry_for_global(global)
                    .and_then(|(_, entry)| entry.precedence)
                    .unwrap_or(255),
                _ => 255,
            },
            Term::Pi { .. } | Term::Lambda { .. } => 10,
            _ => 255,
        }
    }

    /// Canonical source math (§23.5): safe canonical forms, explicit
    /// qualified selectors only when required for disambiguation.
    #[allow(clippy::too_many_lines)]
    fn math(&self, term: &Term, min_prec: u8) -> Result<String, Diagnostic> {
        let own = self.term_prec(term);
        let inner = match term {
            Term::Local(id) => self.spelling(*id),
            Term::NatLiteral { decimal, .. } => decimal.clone(),
            Term::Sort(_) => {
                return Err(fmt_error("a sort has no canonical source spelling"));
            }
            Term::Global(global, _) => match self.entry_for_global(global) {
                Some((qualified, entry)) => match entry
                    .forms
                    .iter()
                    .find(|form| form.canonical_source && form.channel.covers(Channel::Math))
                {
                    Some(form) if entry.surface_arity == 0 => form.surface.clone(),
                    _ => format!("\\lexeme{{{qualified}}}"),
                },
                None => match global {
                    GlobalRef::Document(document) => {
                        format!("\\reference{{{}::{}}}", document.module, document.component)
                    }
                    _ => return Err(fmt_error("no canonical source selector for this global")),
                },
            },
            Term::App {
                function,
                explicit_args,
                ..
            } => match &**function {
                Term::Global(global, _) => match global {
                    GlobalRef::Core(CoreRef::Exists | CoreRef::ExistsUnique) => {
                        return Err(fmt_error(
                            "an existential inside a mathematical island has no source form",
                        ));
                    }
                    _ => match self.entry_for_global(global) {
                        Some((qualified, entry))
                            if entry.surface_arity as usize == explicit_args.len() =>
                        {
                            let form = entry
                                .forms
                                .iter()
                                .find(|form| {
                                    form.canonical_source && form.channel.covers(Channel::Math)
                                })
                                .map(|form| form.surface.clone());
                            match (entry.frame, form, entry.precedence, entry.associativity) {
                                (
                                    crate::lexicon::entry::Frame::Infix,
                                    Some(surface),
                                    Some(precedence),
                                    associativity,
                                ) => {
                                    let left_min = match associativity {
                                        Some(Associativity::Left) => precedence,
                                        _ => precedence + 1,
                                    };
                                    let right_min = match associativity {
                                        Some(Associativity::Right) => precedence,
                                        _ => precedence + 1,
                                    };
                                    format!(
                                        "{} {surface} {}",
                                        self.math(&explicit_args[0], left_min)?,
                                        self.math(&explicit_args[1], right_min)?
                                    )
                                }
                                (
                                    crate::lexicon::entry::Frame::Prefix,
                                    Some(surface),
                                    Some(precedence),
                                    _,
                                ) => format!(
                                    "{surface}{}",
                                    self.math(&explicit_args[0], precedence + 1)?
                                ),
                                (
                                    crate::lexicon::entry::Frame::Postfix,
                                    Some(surface),
                                    Some(precedence),
                                    _,
                                ) => format!(
                                    "{}{surface}",
                                    self.math(&explicit_args[0], precedence + 1)?
                                ),
                                (crate::lexicon::entry::Frame::Call, Some(surface), _, _) => {
                                    let arguments: Result<Vec<String>, Diagnostic> = explicit_args
                                        .iter()
                                        .map(|argument| self.math(argument, 0))
                                        .collect();
                                    format!("{surface}({})", arguments?.join(", "))
                                }
                                _ => {
                                    let arguments: Result<Vec<String>, Diagnostic> = explicit_args
                                        .iter()
                                        .map(|argument| self.math(argument, 0))
                                        .collect();
                                    format!("\\lexeme{{{qualified}}}({})", arguments?.join(", "))
                                }
                            }
                        }
                        _ => {
                            let head = self.math(function, 255)?;
                            let arguments: Result<Vec<String>, Diagnostic> = explicit_args
                                .iter()
                                .map(|argument| self.math(argument, 0))
                                .collect();
                            format!("{head}({})", arguments?.join(", "))
                        }
                    },
                },
                _ => {
                    let head = self.math(function, 255)?;
                    let arguments: Result<Vec<String>, Diagnostic> = explicit_args
                        .iter()
                        .map(|argument| self.math(argument, 0))
                        .collect();
                    format!("{head}({})", arguments?.join(", "))
                }
            },
            Term::Pi { .. } | Term::Lambda { .. } | Term::Let { .. } => {
                return Err(fmt_error("a binder term has no source math form"));
            }
        };
        Ok(if own < min_prec {
            format!("({inner})")
        } else {
            inner
        })
    }

    fn phrase(&self, phrase: &Phrase) -> Result<String, Diagnostic> {
        let mut parts = Vec::new();
        for item in &phrase.items {
            parts.push(match item {
                PhraseItem::Word { entry, form } => {
                    let glossary_entry = self
                        .closure
                        .entry(entry)
                        .ok_or_else(|| fmt_error(format!("`{entry}` is unavailable")))?;
                    glossary_entry
                        .forms
                        .iter()
                        .find(|candidate| candidate.id == *form)
                        .map(|candidate| candidate.surface.clone())
                        .ok_or_else(|| fmt_error("phrase form is unavailable"))?
                }
                PhraseItem::Math(term) => format!("\\({}\\)", self.math(term, 0)?),
                PhraseItem::Punctuation(entry) => match entry.entry.as_str() {
                    "colon" => ":".to_owned(),
                    "hyphen" => "-".to_owned(),
                    "paren-open" => "(".to_owned(),
                    "paren-close" => ")".to_owned(),
                    other => return Err(fmt_error(format!("`{other}` in a phrase"))),
                },
            });
        }
        Ok(parts.join(" "))
    }

    fn binder(&self, binder: &Binder) -> Result<String, Diagnostic> {
        let type_text = match &binder.ty {
            Term::Global(global, _) => match self.entry_for_global(global).and_then(|(_, entry)| {
                entry
                    .forms
                    .iter()
                    .find(|form| form.canonical_source && form.channel.covers(Channel::Text))
                    .map(|form| form.surface.clone())
            }) {
                Some(surface) => surface,
                None => format!("\\({}\\)", self.math(&binder.ty, 0)?),
            },
            other => format!("\\({}\\)", self.math(other, 0)?),
        };
        Ok(format!("{type_text} \\({}\\)", self.spelling(binder.id)))
    }

    fn prose_level(term: &Term) -> u8 {
        match term {
            Term::Pi { .. } => 0,
            Term::App { function, .. } => match &**function {
                Term::Global(GlobalRef::Core(core), _) => match core {
                    CoreRef::Iff => 1,
                    CoreRef::Or => 3,
                    CoreRef::And => 4,
                    CoreRef::Not => 5,
                    CoreRef::Exists | CoreRef::ExistsUnique => 0,
                    CoreRef::Eq => 6,
                },
                _ => 6,
            },
            _ => 6,
        }
    }

    /// Canonical proposition prose in source spelling (§15.6, §23.5).
    #[allow(clippy::too_many_lines)]
    fn prose(&self, term: &Term, initial: bool, level: u8) -> Result<String, Diagnostic> {
        if Self::prose_level(term) < level {
            return Ok(format!("\\({}\\)", self.math(term, 0)?));
        }
        Ok(match term {
            Term::Pi { binders, body }
                if binders.iter().all(|binder| !binder.spelling.is_empty()) =>
            {
                let mut text = String::from(if initial { "For every " } else { "for every " });
                for (index, binder) in binders.iter().enumerate() {
                    if index > 0 {
                        text.push_str(" and ");
                    }
                    text.push_str(&self.binder(binder)?);
                }
                text.push_str(", ");
                text.push_str(&self.prose(body, false, 0)?);
                text
            }
            Term::Pi { binders, body } => {
                let rest = if binders.len() == 1 {
                    (**body).clone()
                } else {
                    Term::Pi {
                        binders: binders[1..].to_vec(),
                        body: body.clone(),
                    }
                };
                format!(
                    "{} {}, then {}",
                    "if",
                    self.prose(&binders[0].ty, false, 1)?,
                    self.prose(&rest, false, 0)?
                )
            }
            Term::App {
                function,
                explicit_args,
                ..
            } => match (&**function, explicit_args.as_slice()) {
                (
                    Term::Global(
                        GlobalRef::Core(core @ (CoreRef::Exists | CoreRef::ExistsUnique)),
                        _,
                    ),
                    [Term::Lambda { binders, body }],
                ) if binders.len() == 1 => {
                    let head = if matches!(core, CoreRef::ExistsUnique) {
                        "there exists exactly one".to_owned()
                    } else {
                        let article = match &binders[0].ty {
                            Term::Global(global, _) => self
                                .entry_for_global(global)
                                .and_then(|(_, entry)| {
                                    entry.forms.iter().find(|form| {
                                        form.canonical_source && form.channel.covers(Channel::Text)
                                    })
                                })
                                .map_or("a", |form| {
                                    if form.features.iter().any(|feature| feature == "article-an") {
                                        "an"
                                    } else {
                                        "a"
                                    }
                                }),
                            _ => "a",
                        };
                        format!("there exists {article}")
                    };
                    format!(
                        "{}{} {} such that {}",
                        if initial {
                            let mut chars = head.chars();
                            match chars.next() {
                                Some(first) => {
                                    first.to_uppercase().collect::<String>() + chars.as_str()
                                }
                                None => head.clone(),
                            }
                        } else {
                            head.clone()
                        },
                        "",
                        self.binder(&binders[0])?,
                        self.prose(body, false, 0)?
                    )
                }
                (Term::Global(GlobalRef::Core(CoreRef::And), _), [left, right]) => format!(
                    "{} and {}",
                    self.prose(left, initial, 4)?,
                    self.prose(right, false, 5)?
                ),
                (Term::Global(GlobalRef::Core(CoreRef::Or), _), [left, right]) => format!(
                    "{} or {}",
                    self.prose(left, initial, 3)?,
                    self.prose(right, false, 4)?
                ),
                (Term::Global(GlobalRef::Core(CoreRef::Not), _), [inner]) => {
                    format!(
                        "{} {}",
                        if initial { "Not" } else { "not" },
                        self.prose(inner, false, 5)?
                    )
                }
                (Term::Global(GlobalRef::Core(CoreRef::Iff), _), [left, right]) => format!(
                    "{} if and only if {}",
                    self.prose(left, initial, 2)?,
                    self.prose(right, false, 2)?
                ),
                _ => format!("\\({}\\)", self.math(term, 0)?),
            },
            _ => format!("\\({}\\)", self.math(term, 0)?),
        })
    }

    fn line(&mut self, depth: usize, text: &str) {
        for _ in 0..depth {
            self.out.push_str("  ");
        }
        self.out.push_str(text);
        self.out.push('\n');
    }

    fn policy_line(&mut self, depth: usize, policy: &AxiomPolicy) {
        match policy {
            AxiomPolicy::None => self.line(depth, "\\noaxioms"),
            AxiomPolicy::Allow(names) => {
                self.line(depth, &format!("\\allowaxioms{{{}}}", names.join(";")));
            }
            AxiomPolicy::Exact(names) => {
                self.line(depth, &format!("\\exactaxioms{{{}}}", names.join(";")));
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn proof_lines(&mut self, proof: &Proof, depth: usize) -> Result<(), Diagnostic> {
        match proof {
            Proof::Sequence(steps) => {
                for step in steps {
                    self.proof_lines(step, depth)?;
                }
            }
            Proof::Intro(locals) => {
                let islands: Vec<String> = locals
                    .iter()
                    .map(|local| format!("\\({}\\)", self.spelling(*local)))
                    .collect();
                self.line(depth, &format!("Assume {}.", islands.join(", ")));
            }
            Proof::Exact(term) => {
                let text = self.math(term, 0)?;
                self.line(depth, &format!("Close the goal with \\({text}\\)."));
            }
            Proof::ApplyOne(term) => {
                let text = self.math(term, 0)?;
                self.line(depth, &format!("Apply \\({text}\\)."));
            }
            Proof::Reflexivity => self.line(depth, "Close the goal by reflexivity."),
            Proof::Witness(term) => {
                let text = self.math(term, 0)?;
                self.line(depth, &format!("Use \\({text}\\) as the witness."));
            }
            Proof::SelectLeft => self.line(depth, "Select the left alternative."),
            Proof::SelectRight => self.line(depth, "Select the right alternative."),
            Proof::Have {
                local,
                proposition,
                proof,
            } => {
                let name = self.spelling(*local);
                self.line(depth, &format!("\\begin{{have}}{{{name}}}"));
                let text = self.prose(proposition, true, 0)?;
                self.line(depth, &format!("{text}."));
                self.line(depth, "\\begin{proof}");
                self.proof_lines(proof, depth)?;
                self.line(depth, "\\end{proof}");
                self.line(depth, "\\end{have}");
            }
            Proof::Rewrite { target, rules } => {
                let target_text = match target {
                    RewriteTarget::Goal => "goal".to_owned(),
                    RewriteTarget::Hypothesis(id) => self.spelling(*id),
                };
                self.line(depth, &format!("\\begin{{rewrite}}{{{target_text}}}"));
                for rule in rules {
                    let text = self.math(&rule.term, 0)?;
                    self.line(
                        depth,
                        &format!(
                            "\\{}{{{text}}}",
                            if rule.reverse { "backward" } else { "forward" }
                        ),
                    );
                }
                self.line(depth, "\\end{rewrite}");
            }
            Proof::SimplifyOnly { target, rules } => {
                let target_text = match target {
                    RewriteTarget::Goal => "goal".to_owned(),
                    RewriteTarget::Hypothesis(id) => self.spelling(*id),
                };
                self.line(depth, &format!("\\begin{{simplify}}{{{target_text}}}"));
                for rule in rules {
                    let text = self.math(rule, 0)?;
                    self.line(depth, &format!("\\rule{{{text}}}"));
                }
                self.line(depth, "\\end{simplify}");
            }
            Proof::Apply { function, premises } => {
                let text = self.math(function, 0)?;
                self.line(depth, &format!("\\begin{{apply}}{{{text}}}"));
                for (index, premise) in premises.iter().enumerate() {
                    self.line(depth, &format!("\\begin{{premise}}{{{}}}", index + 1));
                    self.proof_lines(premise, depth)?;
                    self.line(depth, "\\end{premise}");
                }
                self.line(depth, "\\end{apply}");
            }
            Proof::Constructor(branches) => {
                self.line(depth, "\\begin{constructor}");
                for (index, branch) in branches.iter().enumerate() {
                    self.line(depth, &format!("\\begin{{branch}}{{{}}}", index + 1));
                    self.proof_lines(branch, depth)?;
                    self.line(depth, "\\end{branch}");
                }
                self.line(depth, "\\end{constructor}");
            }
            Proof::Cases { scrutinee, cases } | Proof::Induction { scrutinee, cases } => {
                let env = if matches!(proof, Proof::Cases { .. }) {
                    "cases"
                } else {
                    "induction"
                };
                let text = self.math(scrutinee, 0)?;
                self.line(depth, &format!("\\begin{{{env}}}{{{text}}}"));
                for case in cases {
                    self.line(depth, &format!("\\begin{{case}}{{{}}}", case.constructor));
                    let binds: Vec<String> = case
                        .binders
                        .iter()
                        .map(|(_, spelling)| spelling.clone())
                        .collect();
                    self.line(depth, &format!("\\bind{{{}}}", binds.join(";")));
                    self.proof_lines(&case.proof, depth)?;
                    self.line(depth, "\\end{case}");
                }
                self.line(depth, &format!("\\end{{{env}}}"));
            }
            Proof::Calculate { start, steps, .. } => {
                self.line(depth, "\\begin{calculate}");
                let start_text = self.math(start, 0)?;
                self.line(depth, &format!("\\start{{{start_text}}}"));
                for step in steps {
                    let term = self.math(&step.term, 0)?;
                    let proof_term = self.math(&step.proof, 0)?;
                    self.line(
                        depth,
                        &format!("\\step{{lexlean.core::eq}}{{{term}}}{{{proof_term}}}"),
                    );
                }
                self.line(depth, "\\end{calculate}");
            }
        }
        Ok(())
    }

    fn declaration(&mut self, declaration: &Declaration, depth: usize) -> Result<(), Diagnostic> {
        let env = declaration.kind.as_str();
        match &declaration.body {
            DeclBody::TheoremLike { statement, proof } => {
                self.line(
                    depth,
                    &format!("\\begin{{{env}}}{{{}}}", declaration.component),
                );
                self.policy_line(depth, &declaration.policy);
                let text = self.prose(statement, true, 0)?;
                self.line(depth, &format!("{text}."));
                self.line(depth, "\\begin{proof}");
                self.proof_lines(proof, depth)?;
                self.line(depth, "\\end{proof}");
                self.line(depth, &format!("\\end{{{env}}}"));
            }
            DeclBody::Definition { entry, value, .. } => {
                self.line(
                    depth,
                    &format!("\\begin{{{env}}}{{{}}}{{{entry}}}", declaration.component),
                );
                self.policy_line(depth, &declaration.policy);
                let sentence = self.definition_sentence(declaration, entry, value)?;
                self.line(depth, &sentence);
                self.line(depth, &format!("\\end{{{env}}}"));
            }
        }
        Ok(())
    }

    fn definition_sentence(
        &self,
        declaration: &Declaration,
        entry: &QualifiedId,
        value: &Term,
    ) -> Result<String, Diagnostic> {
        let glossary_entry = self
            .closure
            .entry(entry)
            .ok_or_else(|| fmt_error(format!("`{entry}` is unavailable")))?;
        let (binders, rhs) = match value {
            Term::Lambda { binders, body } => (binders.clone(), (**body).clone()),
            other => (Vec::new(), other.clone()),
        };
        let mut text = String::new();
        if !binders.is_empty() {
            text.push_str("For every ");
            for (index, binder) in binders.iter().enumerate() {
                if index > 0 {
                    text.push_str(" and ");
                }
                text.push_str(&self.binder(binder)?);
            }
            text.push_str(", ");
        }
        let canonical_text = glossary_entry
            .forms
            .iter()
            .find(|form| form.canonical_source && form.channel.covers(Channel::Text))
            .map(|form| form.surface.clone());
        let self_head = if binders.is_empty() && canonical_text.is_some() {
            canonical_text.clone().expect("checked")
        } else {
            // The self application through the entry's own frame and
            // canonical math surface (§15.7 rule 4).
            let math_surface = glossary_entry
                .forms
                .iter()
                .find(|form| form.canonical_source && form.channel.covers(Channel::Math))
                .map(|form| form.surface.clone());
            let argument_spellings: Vec<String> = binders
                .iter()
                .map(|binder| self.spelling(binder.id))
                .collect();
            let inner = match (glossary_entry.frame, &math_surface) {
                (crate::lexicon::entry::Frame::Atom, Some(surface)) => surface.clone(),
                (crate::lexicon::entry::Frame::Call, Some(surface)) => {
                    format!("{surface}({})", argument_spellings.join(", "))
                }
                (crate::lexicon::entry::Frame::Infix, Some(surface))
                    if argument_spellings.len() == 2 =>
                {
                    format!(
                        "{} {surface} {}",
                        argument_spellings[0], argument_spellings[1]
                    )
                }
                (crate::lexicon::entry::Frame::Prefix, Some(surface))
                    if argument_spellings.len() == 1 =>
                {
                    format!("{surface}{}", argument_spellings[0])
                }
                (crate::lexicon::entry::Frame::Postfix, Some(surface))
                    if argument_spellings.len() == 1 =>
                {
                    format!("{}{surface}", argument_spellings[0])
                }
                _ => format!("\\lexeme{{{entry}}}({})", argument_spellings.join(", ")),
            };
            format!("\\({inner}\\)")
        };
        match declaration.kind {
            DeclKind::TypeDefinition => {
                let article = glossary_entry
                    .forms
                    .iter()
                    .find(|form| form.canonical_source && form.channel.covers(Channel::Text))
                    .and_then(|form| {
                        form.features
                            .iter()
                            .find(|feature| feature.starts_with("article-"))
                            .cloned()
                    });
                let article_word = if binders.is_empty() {
                    if article.as_deref() == Some("article-an") {
                        "An "
                    } else {
                        "A "
                    }
                } else if article.as_deref() == Some("article-an") {
                    "an "
                } else {
                    "a "
                };
                let rhs_text = match &rhs {
                    Term::Global(global, _) => {
                        match self.entry_for_global(global).and_then(|(_, rhs_entry)| {
                            rhs_entry
                                .forms
                                .iter()
                                .find(|form| {
                                    form.canonical_source && form.channel.covers(Channel::Text)
                                })
                                .map(|form| form.surface.clone())
                        }) {
                            Some(surface) => surface,
                            None => format!("\\({}\\)", self.math(&rhs, 0)?),
                        }
                    }
                    other => format!("\\({}\\)", self.math(other, 0)?),
                };
                Ok(format!(
                    "{text}{article_word}{self_head} is defined as {rhs_text}."
                ))
            }
            DeclKind::TermDefinition => Ok(format!(
                "{text}{self_head} is defined as \\({}\\).",
                self.math(&rhs, 0)?
            )),
            DeclKind::PredicateDefinition => Ok(format!(
                "{text}{self_head} holds exactly when {}.",
                self.prose(&rhs, false, 0)?
            )),
            _ => Err(fmt_error("theorem-like kind in a definition sentence")),
        }
    }

    fn blocks(&mut self, blocks: &[Block], depth: usize) -> Result<(), Diagnostic> {
        for (index, block) in blocks.iter().enumerate() {
            if index > 0 || depth == 0 {
                self.out.push('\n');
            }
            match block {
                Block::Section(section) => self.section(section, depth)?,
                Block::Declaration(declaration) => self.declaration(declaration, depth)?,
            }
        }
        Ok(())
    }

    fn section(&mut self, section: &Section, depth: usize) -> Result<(), Diagnostic> {
        self.line(
            depth,
            &format!("\\begin{{section}}{{{}}}", section.component),
        );
        let heading = self.phrase(&section.heading)?;
        self.line(depth, &format!("\\heading{{{heading}}}"));
        if !section.params.is_empty() {
            let binders: Result<Vec<String>, Diagnostic> = section
                .params
                .iter()
                .map(|binder| self.binder(binder))
                .collect();
            self.line(depth, &format!("\\parameters{{{}}}", binders?.join("; ")));
        }
        self.blocks(&section.blocks, depth + 1)?;
        self.line(depth, "\\end{section}");
        Ok(())
    }
}

/// Render the canonical source of one checked module (§23.5).
pub fn canonical_source(checked: &CheckedModule, closure: &Closure) -> Result<String, Diagnostic> {
    let document: &DocumentModule = &checked.document;
    let mut spellings = BTreeMap::new();
    crate::backend::latex::collect_spellings_public(document, &mut spellings);
    for (id, spelling) in &checked.proof_spellings {
        spellings.entry(*id).or_insert_with(|| spelling.clone());
    }
    let mut formatter = Fmt {
        closure,
        spellings,
        out: String::new(),
    };
    formatter.line(0, &format!("\\begin{{lexlean}}{{{}}}", document.name));
    let mut glossary = document.glossary.clone();
    glossary.sort();
    for use_row in &glossary {
        formatter.line(0, &format!("\\useglossary{{{use_row}}}"));
    }
    let mut imports = document.imports.clone();
    imports.sort();
    for import in &imports {
        formatter.line(0, &format!("\\importmodule{{{import}}}"));
    }
    let title = formatter.phrase(&document.title)?;
    formatter.line(0, &format!("\\title{{{title}}}"));
    formatter.blocks(&document.blocks, 0)?;
    formatter.line(0, "\\end{lexlean}");
    Ok(formatter.out)
}

/// The definition entry's document declaration is never consulted while
/// formatting; this marker keeps the invariant explicit.
pub const FORMATTER_IS_IR_DRIVEN: bool = true;
