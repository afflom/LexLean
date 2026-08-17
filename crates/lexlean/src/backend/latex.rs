//! The canonical LaTeX backend (SPEC.md §19): rendered solely from linked
//! IR, never copied from source (I8). Every visible word comes from a
//! canonical glossary form, every mathematical construct from LRE and the
//! renderer-token registry, and every structural control from the fixed
//! backend, with complete output coverage (§19.6).
//!
//! Fixed rendering decisions the specification leaves to the backend:
//!
//! - **Deep headings** (§19.3): depth 0 is `\section{...}`, depth 1 is
//!   `\subsection{...}`, and every deeper heading is the registered bold
//!   construct `\textbf{...}` on its own line.
//! - **Section parameters** (§19.3) render immediately below the heading
//!   and its label as one display `\[\mathrm{Parameters}: \forall x \in T;
//!   \forall y \in U\]`, one `\forall x \in T` clause per parameter in
//!   scope order, separated by `;`.
//! - **Calculations** (§19.5) render as one `align*` display with one step
//!   per row: the first row is `start &= t_1 && \text{by } p_1 \\`, every
//!   later row is `&= t_i && \text{by } p_i`, rows separated by `\\`; the
//!   relation glyph is the equality token and the justification is the
//!   step's proof term rendered in math.
//! - **Proof branches** (§19.5) are visible: every `cases`/`induction`
//!   branch opens with `Case <constructor> [with x, y]:`, every
//!   `constructor` branch with `Branch \(i\):`, and every structured
//!   `apply` premise with `Premise \(i\):`, each on its own line before
//!   the branch's own sentences; the words are core glossary entries.
//! - **Sorts** render as `\mathrm{Prop}` / `\mathrm{Type}` through the
//!   registered `sort-prop` / `sort-type` tokens, a numeric level above
//!   `Type` as the subscript `\mathrm{Type}_{n}`; a symbolic level has no
//!   rendering, exactly as it has no Lean lowering.
//! - **Text frames** (§13.4, §19.4) render as canonical prose wherever a
//!   proposition or term is prose: `ARG_0 is SELF`, `ARG_0 SELF`,
//!   `ARG_0 SELF ARG_1`, `the SELF of ARG_0`, and `the SELF of ARG_0 and
//!   ARG_1`, from the entry's canonical text form and the core words `is`,
//!   `the`, `of`, and `and`; an entry's `[render] text` template replaces
//!   the fixed pattern. Noun-phrase arguments nest as prose, every other
//!   argument is a math island. A document declaration is named through
//!   the unique visible entry denoting it. A sentence-initial noun phrase
//!   takes the sentence-case `The`, like every other sentence-initial core
//!   word.
//! - **Phrase punctuation** (§15.3) is spaced as canonical source spells
//!   it: no space before `:` or `)`, none after `(`, and a tight hyphen.
//! - **Case labels** name the constructor by its canonical text form when
//!   it has one; otherwise its math head as an island, exactly as it
//!   renders in a term: an atom's math render, else its canonical math
//!   surface as `\operatorname{...}` when the constructor takes surface
//!   arguments (its LRE head is an operator name) and plain when it is an
//!   atom.
//! - **Quantified operands** (§15.6, §23.5) follow the source formatter's
//!   trailing rule: a quantified proposition reads to the end of its
//!   sentence, so it is prose only in trailing position (the right operand
//!   of a connective, a body, an antecedent, a `have` statement) and a
//!   math island elsewhere; the island states every binder's type
//!   (`\forall x \in T, ...`, `\exists x \in T, ...`).
//! - **Document references** no visible entry names render as
//!   `\texttt{Module::component}` under the reference coverage origin, the
//!   escape form of qualified selectors, unapplied and applied alike; the
//!   Lean name never appears (its `_` would be a subscript in math).
//! - **Heads without a saturated render** (an entry with only a text word,
//!   such as a type noun defined as a sort) render that word as
//!   `\text{...}`, so a section parameter typed by it reads `\forall T \in
//!   \text{type}`.

use std::collections::{BTreeMap, BTreeSet};

use crate::artifact::source_map::MapRole;
use crate::backend::{EmitSource, Emitter};
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::ir::declaration::{DeclBody, DeclKind, Declaration};
use crate::ir::document::{Block, DocumentModule, Phrase, PhraseItem};
use crate::ir::proof::{Proof, RewriteTarget};
use crate::ir::term::{Binder, CoreRef, GlobalRef, LocalId, Term};
use crate::lexicon::entry::{Channel, Denotation, Entry, Frame};
use crate::lexicon::lre::Render;
use crate::lexicon::lse::QualifiedId;
use crate::lexicon::resolve::Closure;
use crate::link::{CheckedModule, DeclOrigin};
use crate::source::coverage::Origin;

/// The renderer context for one module.
struct Ctx<'a> {
    closure: &'a Closure,
    /// Display spellings by local identity.
    spellings: BTreeMap<LocalId, String>,
    /// The visible glossary entry whose document denotation names each
    /// `(module, component)`, when exactly one visible entry does (§15.7:
    /// a document declaration is named in prose through that entry).
    document_entries: BTreeMap<(String, String), Option<QualifiedId>>,
}

impl<'a> Ctx<'a> {
    fn new(
        closure: &'a Closure,
        visible: &BTreeSet<String>,
        spellings: BTreeMap<LocalId, String>,
    ) -> Self {
        let mut document_entries: BTreeMap<(String, String), Option<QualifiedId>> = BTreeMap::new();
        for package in &closure.packages {
            if !visible.contains(&package.id) {
                continue;
            }
            for (entry_id, entry) in &package.entries {
                if let Denotation::Document { module, component } = &entry.denotation {
                    let qualified = QualifiedId {
                        package: package.id.clone(),
                        entry: entry_id.clone(),
                    };
                    document_entries
                        .entry((module.clone(), component.clone()))
                        .and_modify(|slot| *slot = None)
                        .or_insert(Some(qualified));
                }
            }
        }
        Self {
            closure,
            spellings,
            document_entries,
        }
    }
}

/// A LaTeX token sink bound to one origin context.
struct Sink<'a, 'c> {
    emitter: &'a mut Emitter,
    ctx: &'a Ctx<'c>,
    source: EmitSource,
    role: MapRole,
    node: usize,
}

impl Sink<'_, '_> {
    /// Emit one renderer token by registry ID (§13.10).
    fn tok(&mut self, id: &str) -> Result<(), Diagnostic> {
        let row = self.ctx.closure.registry.get(id).ok_or_else(|| {
            Diagnostic::new(
                code!("LLB6002"),
                format!("renderer token `{id}` is not in the registry"),
            )
        })?;
        let kind = if row.bytes.starts_with('\\') {
            "control"
        } else if row.bytes.chars().all(|c| c.is_ascii_alphanumeric()) {
            "word"
        } else {
            "punctuation"
        };
        let bytes = row.bytes.clone();
        // Renderer-token output carries the `renderer` role (§20.3) except
        // inside the synthetic preamble, which stays `synthetic`.
        let role = if self.role == MapRole::Synthetic {
            MapRole::Synthetic
        } else {
            MapRole::Renderer
        };
        self.emitter.piece(
            &bytes,
            kind,
            Origin::RendererToken(id.to_owned()),
            self.source.clone(),
            role,
            self.node,
        );
        Ok(())
    }

    /// Emit a structural brace covered by the core entries.
    fn brace(&mut self, open: bool) {
        self.emitter.piece(
            if open { "{" } else { "}" },
            "delimiter",
            Origin::Structural {
                package: "lexlean.core".to_owned(),
                entry: if open { "brace-open" } else { "brace-close" }.to_owned(),
            },
            self.source.clone(),
            self.role,
            self.node,
        );
    }

    fn structural(&mut self, text: &str, entry: &str, kind: &str) {
        // Control sequences map under the `renderer` role (§20.3);
        // punctuation keeps the enclosing role.
        let role = if kind == "control" && self.role != MapRole::Synthetic {
            MapRole::Renderer
        } else {
            self.role
        };
        self.emitter.piece(
            text,
            kind,
            Origin::Structural {
                package: "lexlean.core".to_owned(),
                entry: entry.to_owned(),
            },
            self.source.clone(),
            role,
            self.node,
        );
    }

    /// Emit one core grammar word through its canonical form (§19.5: these
    /// words are core glossary entries; the renderer never invents
    /// synonyms). `capitalized` selects the sentence-case form.
    fn word(&mut self, entry_id: &str, capitalized: bool) -> Result<(), Diagnostic> {
        let qualified = QualifiedId {
            package: "lexlean.core".to_owned(),
            entry: entry_id.to_owned(),
        };
        let entry = self.ctx.closure.entry(&qualified).ok_or_else(|| {
            Diagnostic::new(
                code!("LLB6002"),
                format!("core word `{entry_id}` is not in the glossary"),
            )
        })?;
        let form = entry
            .forms
            .iter()
            .find(|form| {
                let is_upper = form
                    .surface
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_ascii_uppercase());
                is_upper == capitalized
            })
            .or_else(|| entry.forms.first())
            .ok_or_else(|| {
                Diagnostic::new(
                    code!("LLB6002"),
                    format!("core word `{entry_id}` has no form"),
                )
            })?;
        let surface = form.surface.clone();
        let form_id = form.id.clone();
        self.emitter.piece(
            &surface,
            "word",
            Origin::Form {
                package: "lexlean.core".to_owned(),
                entry: entry_id.to_owned(),
                form: form_id,
            },
            self.source.clone(),
            self.role,
            self.node,
        );
        Ok(())
    }

    /// Emit a glossary form's surface.
    fn form_surface(
        &mut self,
        package: &str,
        entry: &str,
        form_id: &str,
    ) -> Result<(), Diagnostic> {
        let qualified = QualifiedId {
            package: package.to_owned(),
            entry: entry.to_owned(),
        };
        let glossary_entry = self.ctx.closure.entry(&qualified).ok_or_else(|| {
            Diagnostic::new(code!("LLB6002"), format!("`{qualified}` is unavailable"))
        })?;
        let form = glossary_entry
            .forms
            .iter()
            .find(|form| form.id == form_id)
            .or_else(|| {
                glossary_entry
                    .forms
                    .iter()
                    .find(|form| form.canonical_source)
            })
            .ok_or_else(|| {
                Diagnostic::new(code!("LLB6002"), format!("`{qualified}` has no form"))
            })?;
        // Defense in depth (§13.9, §19.1): only a renderer-safe spelling
        // reaches the document. A control-sequence alias selected in the
        // source renders as the entry's canonical form of the same channel.
        let form = if crate::lexicon::entry::surface_safety(&form.atoms, form.channel).is_ok() {
            form
        } else {
            glossary_entry
                .forms
                .iter()
                .find(|candidate| {
                    candidate.canonical_source
                        && candidate.channel.covers(form.channel)
                        && crate::lexicon::entry::surface_safety(
                            &candidate.atoms,
                            candidate.channel,
                        )
                        .is_ok()
                })
                .ok_or_else(|| {
                    Diagnostic::new(
                        code!("LLB6002"),
                        format!(
                            "`{qualified}`: form `{}` is not renderer-safe and no renderer-safe canonical form replaces it",
                            form.id
                        ),
                    )
                })?
        };
        let surface = form.surface.clone();
        let chosen = form.id.clone();
        self.emitter.piece(
            &surface,
            "word",
            Origin::Form {
                package: package.to_owned(),
                entry: entry.to_owned(),
                form: chosen,
            },
            self.source.clone(),
            self.role,
            self.node,
        );
        Ok(())
    }

    /// Emit a local by its display spelling. Every rendered local has a
    /// spelling in the linked IR (binders and proof introductions record
    /// theirs); a missing one is an internal invariant failure, never an
    /// invented name.
    fn local(&mut self, id: LocalId) -> Result<(), Diagnostic> {
        let spelling = self.ctx.spellings.get(&id).cloned().ok_or_else(|| {
            Diagnostic::new(
                code!("LLI9001"),
                format!("phase latex: local {} has no display spelling", id.0),
            )
        })?;
        self.emitter.piece(
            &spelling,
            "word",
            Origin::Local(id.0 as usize),
            self.source.clone(),
            self.role,
            self.node,
        );
        Ok(())
    }

    fn numeral(&mut self, digits: &str) {
        self.emitter.piece(
            digits,
            "numeral",
            Origin::Numeral,
            self.source.clone(),
            self.role,
            self.node,
        );
    }

    fn metadata(&mut self, text: &str, owner: &str) {
        self.emitter.piece(
            text,
            "word",
            Origin::Metadata {
                owner: owner.to_owned(),
            },
            self.source.clone(),
            self.role,
            self.node,
        );
    }

    /// Emit a document reference `Module::component` (§17.2) under its own
    /// coverage origin, distinct from structural metadata.
    fn reference(&mut self, module: &str, component: &str) {
        self.emitter.piece(
            &format!("{module}::{component}"),
            "word",
            Origin::Reference {
                module: module.to_owned(),
                component: component.to_owned(),
            },
            self.source.clone(),
            self.role,
            self.node,
        );
    }

    fn ws(&mut self, text: &str) {
        self.emitter.ws(text);
    }
}

/// The glossary entry for a global, for LRE-driven rendering: core
/// constructors and lexicon entries by identity, document declarations
/// through the unique visible entry denoting them.
fn entry_for_global<'c>(ctx: &Ctx<'c>, global: &GlobalRef) -> Option<(QualifiedId, &'c Entry)> {
    let closure = ctx.closure;
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
        GlobalRef::Document(document) => ctx
            .document_entries
            .get(&(document.module.clone(), document.component.clone()))
            .cloned()
            .flatten()?,
    };
    let entry = closure.entry(&qualified)?;
    Some((qualified, entry))
}

/// The top-level operator precedence of a term for parenthesization, 255
/// for atoms.
fn term_prec(ctx: &Ctx<'_>, term: &Term) -> Result<u8, Diagnostic> {
    Ok(match term {
        // A form printed through its operator render binds at its declared
        // precedence; a head printed as a call or qualified selector (an
        // arity mismatch) is atomic, so it takes no parentheses.
        Term::App {
            function,
            explicit_args,
            ..
        } => match &**function {
            Term::Global(global, _) => entry_for_global(ctx, global)
                .filter(|(_, entry)| entry.surface_arity as usize == explicit_args.len())
                .and_then(|(_, entry)| entry.precedence)
                .unwrap_or(255),
            _ => 255,
        },
        // An implication binds at the core arrow's precedence; a quantifier
        // or lambda body extends to the end of its island.
        Term::Pi { binders, .. } if binders.iter().all(|binder| binder.spelling.is_empty()) => {
            arrow_precedence(ctx)?
        }
        Term::Pi { .. } | Term::Lambda { .. } => 10,
        _ => 255,
    })
}

/// The registered precedence of the core arrow `lexlean.core::arrow`
/// (§13.10), which the implication island honors: right associative, its
/// antecedent one level tighter. Read from the closure so the language
/// data stays the single source.
fn arrow_precedence(ctx: &Ctx<'_>) -> Result<u8, Diagnostic> {
    let arrow = QualifiedId {
        package: "lexlean.core".to_owned(),
        entry: "arrow".to_owned(),
    };
    ctx.closure
        .entry(&arrow)
        .and_then(|entry| entry.precedence)
        .ok_or_else(|| {
            Diagnostic::new(
                code!("LLB6002"),
                "core entry `lexlean.core::arrow` declares no precedence for the implication island",
            )
        })
}

/// The canonical math form ID of an entry, when it has one.
fn math_form_id(entry: &Entry) -> Option<String> {
    entry
        .forms
        .iter()
        .find(|form| form.canonical_source && form.channel.covers(Channel::Math))
        .map(|form| form.id.clone())
}

/// An entry's head in math without an applicable saturated LRE render
/// (module documentation): its arity-zero math render when it stands
/// alone; else its canonical math form, as `\operatorname{...}` when the
/// entry takes surface arguments or is applied (its LRE head is an
/// operator name) and plain when it is an atom; else its canonical text
/// word as `\text{...}` (a type noun defined as a sort, a text-frame
/// predicate forced into an island); else the qualified escape form.
/// `applied` says the head is followed by an argument list, so an
/// arity-zero render does not apply.
fn math_head(
    sink: &mut Sink<'_, '_>,
    qualified: &QualifiedId,
    entry: &Entry,
    applied: bool,
) -> Result<(), Diagnostic> {
    let atom_render = entry
        .render_math
        .clone()
        .filter(|_| entry.surface_arity == 0 && !applied);
    if let Some(render) = atom_render {
        eval_lre(sink, &render, qualified, &[])
    } else if let Some(form_id) = math_form_id(entry) {
        let operator = entry.surface_arity > 0 || applied;
        if operator {
            sink.tok("operatorname")?;
            sink.brace(true);
        }
        sink.form_surface(&qualified.package, &qualified.entry, &form_id)?;
        if operator {
            sink.brace(false);
        }
        Ok(())
    } else if let Some(form_id) = text_form_id(entry) {
        sink.tok("text")?;
        sink.brace(true);
        sink.form_surface(&qualified.package, &qualified.entry, &form_id)?;
        sink.brace(false);
        Ok(())
    } else {
        fallback_qualified(sink, qualified)
    }
}

/// A sort in math (module documentation): `\mathrm{Prop}`, `\mathrm{Type}`,
/// and `\mathrm{Type}_{n}` for the numeric level `Type n`. A symbolic
/// level has no canonical LaTeX rendering, exactly as it has no Lean
/// lowering in a document term (LLB6001): language 1.0 documents state
/// their universes numerically.
fn sort(sink: &mut Sink<'_, '_>, universe: &crate::ir::term::Universe) -> Result<(), Diagnostic> {
    use crate::ir::term::Universe;
    let level = match universe {
        Universe::Num(0) => {
            sink.tok("mathrm")?;
            sink.brace(true);
            sink.tok("sort-prop")?;
            sink.brace(false);
            return Ok(());
        }
        Universe::Num(n) => n.checked_sub(1).ok_or_else(|| {
            Diagnostic::new(code!("LLI9001"), "phase latex: universe level underflow")
        })?,
        Universe::Var(_) | Universe::Succ(_) | Universe::Max(_) | Universe::IMax(..) => {
            return Err(Diagnostic::new(
                code!("LLB6002"),
                "a sort at a symbolic universe level has no canonical LaTeX rendering in language 1.0",
            ));
        }
    };
    sink.tok("mathrm")?;
    sink.brace(true);
    sink.tok("sort-type")?;
    sink.brace(false);
    if level > 0 {
        sink.tok("subscript")?;
        sink.brace(true);
        sink.numeral(&level.to_string());
        sink.brace(false);
    }
    Ok(())
}

/// A typed quantifier prefix in math: `\forall x \in T` / `\exists x \in
/// T` per binder, binders separated by `, `, closed by `, ` before the
/// body. The binder type is stated (module documentation): a quantified
/// proposition that must be an island keeps the information its prose form
/// carries in the type noun.
fn quantifier_prefix(
    sink: &mut Sink<'_, '_>,
    token: &str,
    binders: &[Binder],
) -> Result<(), Diagnostic> {
    for (index, binder) in binders.iter().enumerate() {
        if index > 0 {
            sink.tok("comma")?;
            sink.ws(" ");
        }
        sink.tok(token)?;
        sink.ws(" ");
        sink.local(binder.id)?;
        sink.ws(" ");
        sink.tok("member")?;
        sink.ws(" ");
        math_term(sink, &binder.ty, 255)?;
    }
    sink.tok("comma")?;
    sink.ws(" ");
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn math_term(sink: &mut Sink<'_, '_>, term: &Term, min_prec: u8) -> Result<(), Diagnostic> {
    let ctx = sink.ctx;
    let own_prec = term_prec(ctx, term)?;
    let needs_parens = own_prec < min_prec;
    if needs_parens {
        sink.tok("left-paren")?;
    }
    match term {
        Term::Local(id) => sink.local(*id)?,
        Term::NatLiteral { decimal, .. } => sink.numeral(decimal),
        Term::Sort(universe) => sort(sink, universe)?,
        Term::Global(global, _) => match entry_for_global(ctx, global) {
            Some((qualified, entry)) => math_head(sink, &qualified, entry, false)?,
            None => fallback_global(sink, global)?,
        },
        // An application with no explicit arguments (an atom whose implicit
        // parameters were instantiated) renders as the atom.
        Term::App {
            function,
            explicit_args,
            ..
        } if explicit_args.is_empty() => math_term(sink, function, min_prec)?,
        Term::App {
            function,
            explicit_args,
            ..
        } => match &**function {
            Term::Global(global, _) => match global {
                GlobalRef::Core(CoreRef::Exists | CoreRef::ExistsUnique)
                    if explicit_args.len() == 1 =>
                {
                    let unique = matches!(global, GlobalRef::Core(CoreRef::ExistsUnique));
                    let token = if unique { "exists-unique" } else { "exists" };
                    if let Term::Lambda { binders, body } = &explicit_args[0] {
                        quantifier_prefix(sink, token, binders)?;
                        math_term(sink, body, 0)?;
                    } else {
                        sink.tok(token)?;
                        sink.ws(" ");
                        math_term(sink, &explicit_args[0], 255)?;
                    }
                }
                _ => match entry_for_global(ctx, global) {
                    Some((qualified, entry))
                        if entry.render_math.is_some()
                            && entry.surface_arity as usize == explicit_args.len() =>
                    {
                        let render = entry.render_math.clone().expect("checked");
                        let precedence = entry.precedence;
                        let associativity = entry.associativity;
                        let arg_specs: Vec<(Term, u8)> = explicit_args
                            .iter()
                            .enumerate()
                            .map(|(index, argument)| {
                                let required = match (precedence, associativity) {
                                    (Some(op), Some(assoc)) => {
                                        use crate::lexicon::entry::Associativity;
                                        let left_min = match assoc {
                                            Associativity::Left => op,
                                            _ => op.saturating_add(1),
                                        };
                                        let right_min = match assoc {
                                            Associativity::Right => op,
                                            _ => op.saturating_add(1),
                                        };
                                        if index == 0 {
                                            left_min
                                        } else {
                                            right_min
                                        }
                                    }
                                    (Some(op), None) => op.saturating_add(1),
                                    _ => 0,
                                };
                                (argument.clone(), required)
                            })
                            .collect();
                        eval_lre(sink, &render, &qualified, &arg_specs)?;
                    }
                    _ => {
                        // Fallback: the head's own rendering (an entry by
                        // its canonical form, a document reference no entry
                        // names as `\texttt{Module::component}`, exactly as
                        // it renders unapplied) with a parenthesized
                        // argument list.
                        match entry_for_global(ctx, global) {
                            Some((qualified, entry)) => {
                                math_head(sink, &qualified, entry, true)?;
                            }
                            None => fallback_global(sink, global)?,
                        }
                        sink.tok("left-paren")?;
                        for (index, argument) in explicit_args.iter().enumerate() {
                            if index > 0 {
                                sink.tok("comma")?;
                                sink.ws(" ");
                            }
                            math_term(sink, argument, 0)?;
                        }
                        sink.tok("right-paren")?;
                    }
                },
            },
            _ => {
                math_term(sink, function, 255)?;
                sink.tok("left-paren")?;
                for (index, argument) in explicit_args.iter().enumerate() {
                    if index > 0 {
                        sink.tok("comma")?;
                        sink.ws(" ");
                    }
                    math_term(sink, argument, 0)?;
                }
                sink.tok("right-paren")?;
            }
        },
        Term::Pi { binders, body } => {
            let named = binders
                .iter()
                .take_while(|binder| !binder.spelling.is_empty())
                .count();
            let rest = |from: usize| {
                if from == binders.len() {
                    (**body).clone()
                } else {
                    Term::Pi {
                        binders: binders[from..].to_vec(),
                        body: body.clone(),
                    }
                }
            };
            if named == 0 {
                // Implication: the core arrow, right associative at its
                // registered precedence (§13.10).
                let arrow = arrow_precedence(ctx)?;
                math_term(sink, &binders[0].ty, arrow.saturating_add(1))?;
                sink.ws(" ");
                sink.tok("implies")?;
                sink.ws(" ");
                math_term(sink, &rest(1), arrow)?;
            } else {
                // Universal quantification with typed binders; an anonymous
                // remainder is the implication that follows.
                quantifier_prefix(sink, "forall", &binders[..named])?;
                math_term(sink, &rest(named), 0)?;
            }
        }
        Term::Lambda { binders, body } => {
            for binder in binders {
                sink.local(binder.id)?;
                sink.ws(" ");
            }
            sink.tok("mapsto")?;
            sink.ws(" ");
            math_term(sink, body, 0)?;
        }
        Term::Let { .. } => {
            return Err(Diagnostic::new(
                code!("LLB6002"),
                "a let term has no canonical LaTeX rendering in language 1.0",
            ));
        }
    }
    if needs_parens {
        sink.tok("right-paren")?;
    }
    Ok(())
}

fn fallback_global(sink: &mut Sink<'_, '_>, global: &GlobalRef) -> Result<(), Diagnostic> {
    match global {
        GlobalRef::Core(core) => {
            sink.tok(match core {
                CoreRef::Eq => "equals",
                CoreRef::And => "logical-and",
                CoreRef::Or => "logical-or",
                CoreRef::Not => "logical-not",
                CoreRef::Iff => "iff",
                CoreRef::Exists => "exists",
                CoreRef::ExistsUnique => "exists-unique",
            })?;
            Ok(())
        }
        GlobalRef::External(external) => {
            let qualified = QualifiedId::parse(&external.entry).map_err(|reason| {
                Diagnostic::new(code!("LLI9001"), format!("phase latex: {reason}"))
            })?;
            fallback_qualified(sink, &qualified)
        }
        GlobalRef::DefinedLexicon(defined) => {
            let qualified = QualifiedId::parse(&defined.entry).map_err(|reason| {
                Diagnostic::new(code!("LLI9001"), format!("phase latex: {reason}"))
            })?;
            fallback_qualified(sink, &qualified)
        }
        GlobalRef::Document(document) => {
            // A declaration no visible entry names renders by its
            // reference `Module::component`, the escape form of qualified
            // selectors: module names and component IDs (§15.2) contain no
            // byte TeX must escape, where the Lean name's `_` would be a
            // subscript in math.
            sink.tok("texttt")?;
            sink.brace(true);
            sink.reference(&document.module, &document.component);
            sink.brace(false);
            Ok(())
        }
    }
}

/// The `\texttt{qualified-id}` fallback when no safe canonical surface
/// exists (§13.5 rule 6 analogue for output).
fn fallback_qualified(sink: &mut Sink<'_, '_>, qualified: &QualifiedId) -> Result<(), Diagnostic> {
    sink.tok("texttt")?;
    sink.brace(true);
    sink.metadata(&qualified.to_string(), &qualified.to_string());
    sink.brace(false);
    Ok(())
}

/// Evaluate one LRE template (§13.9).
fn eval_lre(
    sink: &mut Sink<'_, '_>,
    render: &Render,
    self_entry: &QualifiedId,
    args: &[(Term, u8)],
) -> Result<(), Diagnostic> {
    match render {
        Render::Seq(items) => {
            for item in items {
                eval_lre(sink, item, self_entry, args)?;
            }
        }
        Render::Space => sink.ws(" "),
        Render::Token(id) => sink.tok(id)?,
        Render::Slot(index) => {
            let (term, min_prec) = args
                .get(*index as usize)
                .ok_or_else(|| Diagnostic::new(code!("LLB6002"), "render slot out of range"))?;
            math_term(sink, term, *min_prec)?;
        }
        Render::SelfForm(form_id) => {
            sink.form_surface(&self_entry.package, &self_entry.entry, form_id)?;
        }
        Render::Form { entry, form } => {
            sink.form_surface(&entry.package, &entry.entry, form)?;
        }
        Render::Group(inner) => {
            sink.brace(true);
            eval_lre(sink, inner, self_entry, args)?;
            sink.brace(false);
        }
        Render::Paren(inner) => {
            sink.tok("left-paren")?;
            eval_lre(sink, inner, self_entry, args)?;
            sink.tok("right-paren")?;
        }
        Render::Bracket(inner) => {
            sink.tok("left-bracket")?;
            eval_lre(sink, inner, self_entry, args)?;
            sink.tok("right-bracket")?;
        }
        Render::OperatorName(name) => {
            sink.tok("operatorname")?;
            sink.brace(true);
            sink.metadata(name, &self_entry.to_string());
            sink.brace(false);
        }
        Render::Sub(base, script) | Render::Sup(base, script) => {
            // `base_{script}` / `base^{script}`: the base is grouped so
            // multi-token bases attach the script as one unit.
            sink.brace(true);
            eval_lre(sink, base, self_entry, args)?;
            sink.brace(false);
            sink.tok(if matches!(render, Render::Sub(..)) {
                "subscript"
            } else {
                "superscript"
            })?;
            sink.brace(true);
            eval_lre(sink, script, self_entry, args)?;
            sink.brace(false);
        }
        Render::Frac(numerator, denominator) => {
            sink.tok("frac")?;
            sink.brace(true);
            eval_lre(sink, numerator, self_entry, args)?;
            sink.brace(false);
            sink.brace(true);
            eval_lre(sink, denominator, self_entry, args)?;
            sink.brace(false);
        }
    }
    Ok(())
}

/// The prose precedence levels of §15.6, used to decide when a child must
/// become a math island so that reparsing preserves the IR (§19.4).
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

fn island(sink: &mut Sink<'_, '_>, term: &Term, display: bool) -> Result<(), Diagnostic> {
    sink.structural(
        if display { "\\[" } else { "\\(" },
        if display { "display-open" } else { "math-open" },
        "control",
    );
    math_term(sink, term, 0)?;
    sink.structural(
        if display { "\\]" } else { "\\)" },
        if display {
            "display-close"
        } else {
            "math-close"
        },
        "control",
    );
    Ok(())
}

/// The canonical text form ID of an entry, when it has one.
fn text_form_id(entry: &Entry) -> Option<String> {
    entry
        .forms
        .iter()
        .find(|form| form.canonical_source && form.channel.covers(Channel::Text))
        .map(|form| form.id.clone())
}

/// A text-frame application (§13.4): the entry, its qualified ID, and the
/// explicit arguments, when `term` applies (or is) an entry whose frame is
/// one of `frames`, whose surface arity matches, and which has a canonical
/// text form.
fn text_frame_of<'c, 't>(
    ctx: &Ctx<'c>,
    term: &'t Term,
    frames: &[Frame],
) -> Option<(QualifiedId, &'c Entry, &'t [Term])> {
    let (function, args): (&Term, &[Term]) = match term {
        Term::App {
            function,
            explicit_args,
            ..
        } => (function, explicit_args),
        other => (other, &[]),
    };
    let Term::Global(global, _) = function else {
        return None;
    };
    let (qualified, entry) = entry_for_global(ctx, global)?;
    if !frames.contains(&entry.frame) || entry.surface_arity as usize != args.len() {
        return None;
    }
    text_form_id(entry)?;
    Some((qualified, entry, args))
}

/// The `i`th explicit argument of a text frame; the arity was matched
/// before the frame was selected, so a miss is an internal invariant
/// failure.
fn frame_arg(args: &[Term], index: usize) -> Result<&Term, Diagnostic> {
    args.get(index).ok_or_else(|| {
        Diagnostic::new(
            code!("LLI9001"),
            format!("phase latex: text frame argument {index} is missing"),
        )
    })
}

/// Render a text frame (§13.4) as canonical prose: the entry's text render
/// template when it declares one (§13.9), otherwise the frame's fixed
/// pattern with the core words `the`, `of`, `and`, and `is`. Arguments
/// that are noun phrases nest as prose; other arguments are math islands.
/// `initial` capitalizes a leading core word.
fn text_frame(
    sink: &mut Sink<'_, '_>,
    qualified: &QualifiedId,
    entry: &Entry,
    args: &[Term],
    initial: bool,
) -> Result<(), Diagnostic> {
    if let Some(render) = entry.render_text.clone() {
        return eval_text_lre(sink, &render, qualified, args);
    }
    let form_id = text_form_id(entry).ok_or_else(|| {
        Diagnostic::new(
            code!("LLB6002"),
            format!("`{qualified}` has no canonical text form"),
        )
    })?;
    match entry.frame {
        Frame::NounOf | Frame::BinaryNounOf => {
            sink.word("the", initial)?;
            sink.ws(" ");
            sink.form_surface(&qualified.package, &qualified.entry, &form_id)?;
            sink.ws(" ");
            sink.word("of", false)?;
            sink.ws(" ");
            term_phrase(sink, frame_arg(args, 0)?, false)?;
            if entry.frame == Frame::BinaryNounOf {
                sink.ws(" ");
                sink.word("and", false)?;
                sink.ws(" ");
                term_phrase(sink, frame_arg(args, 1)?, false)?;
            }
        }
        Frame::Adjective => {
            term_phrase(sink, frame_arg(args, 0)?, initial)?;
            sink.ws(" ");
            sink.word("is", false)?;
            sink.ws(" ");
            sink.form_surface(&qualified.package, &qualified.entry, &form_id)?;
        }
        Frame::Intransitive | Frame::Transitive => {
            term_phrase(sink, frame_arg(args, 0)?, initial)?;
            sink.ws(" ");
            sink.form_surface(&qualified.package, &qualified.entry, &form_id)?;
            if entry.frame == Frame::Transitive {
                sink.ws(" ");
                term_phrase(sink, frame_arg(args, 1)?, false)?;
            }
        }
        Frame::Atom => {
            sink.form_surface(&qualified.package, &qualified.entry, &form_id)?;
        }
        Frame::Call | Frame::Prefix | Frame::Postfix | Frame::Infix => {
            return Err(Diagnostic::new(
                code!("LLI9001"),
                format!("phase latex: `{qualified}` has a mathematical frame, not a text frame"),
            ));
        }
    }
    Ok(())
}

/// The frames whose canonical rendering is prose (§13.4): the text frames
/// and the atom of a text-canonical entry.
const TEXT_FRAMES: [Frame; 6] = [
    Frame::Atom,
    Frame::NounOf,
    Frame::BinaryNounOf,
    Frame::Adjective,
    Frame::Intransitive,
    Frame::Transitive,
];

/// Evaluate one text render template (§13.9): slots are nested term
/// phrases; the mathematical constructs `sub`, `sup`, `frac`, and
/// `operator-name` have no text rendering.
fn eval_text_lre(
    sink: &mut Sink<'_, '_>,
    render: &Render,
    self_entry: &QualifiedId,
    args: &[Term],
) -> Result<(), Diagnostic> {
    match render {
        Render::Seq(items) => {
            for item in items {
                eval_text_lre(sink, item, self_entry, args)?;
            }
        }
        Render::Space => sink.ws(" "),
        Render::Token(id) => sink.tok(id)?,
        Render::Slot(index) => {
            let term = args.get(*index as usize).ok_or_else(|| {
                Diagnostic::new(code!("LLB6002"), "text render slot out of range")
            })?;
            term_phrase(sink, term, false)?;
        }
        Render::SelfForm(form_id) => {
            sink.form_surface(&self_entry.package, &self_entry.entry, form_id)?;
        }
        Render::Form { entry, form } => {
            sink.form_surface(&entry.package, &entry.entry, form)?;
        }
        Render::Group(inner) => {
            sink.brace(true);
            eval_text_lre(sink, inner, self_entry, args)?;
            sink.brace(false);
        }
        Render::Paren(inner) => {
            sink.structural("(", "paren-open", "punctuation");
            eval_text_lre(sink, inner, self_entry, args)?;
            sink.structural(")", "paren-close", "punctuation");
        }
        Render::Bracket(inner) => {
            sink.structural("[", "bracket-open", "punctuation");
            eval_text_lre(sink, inner, self_entry, args)?;
            sink.structural("]", "bracket-close", "punctuation");
        }
        Render::Sub(..) | Render::Sup(..) | Render::Frac(..) | Render::OperatorName(_) => {
            return Err(Diagnostic::new(
                code!("LLB6002"),
                format!(
                    "the text render of `{self_entry}` uses a mathematical construct that has no text rendering"
                ),
            ));
        }
    }
    Ok(())
}

/// A term in a text position (§15.3, §13.4): the noun-of frame `the SELF
/// of ARG [and ARG]` when the term applies a noun-function entry, otherwise
/// a mathematical island.
fn term_phrase(sink: &mut Sink<'_, '_>, term: &Term, initial: bool) -> Result<(), Diagnostic> {
    match text_frame_of(sink.ctx, term, &[Frame::NounOf, Frame::BinaryNounOf]) {
        Some((qualified, entry, args)) => text_frame(sink, &qualified, entry, args, initial),
        None => island(sink, term, false),
    }
}

/// A type in a text position (§15.3): the type-noun's canonical text form
/// when the type is one such entry, otherwise a mathematical island.
fn type_prose(sink: &mut Sink<'_, '_>, ty: &Term) -> Result<(), Diagnostic> {
    match text_frame_of(sink.ctx, ty, &[Frame::Atom]) {
        Some((qualified, entry, args)) => text_frame(sink, &qualified, entry, args, false),
        None => island(sink, ty, false),
    }
}

/// An atomic proposition (§15.6): a predicate frame `ARG is SELF`, `ARG
/// SELF`, or `ARG SELF ARG` when the term applies a text-predicate entry,
/// otherwise a math proposition island.
fn atomic_prose(sink: &mut Sink<'_, '_>, term: &Term, initial: bool) -> Result<(), Diagnostic> {
    match text_frame_of(
        sink.ctx,
        term,
        &[Frame::Adjective, Frame::Intransitive, Frame::Transitive],
    ) {
        Some((qualified, entry, args)) => text_frame(sink, &qualified, entry, args, initial),
        None => island(sink, term, false),
    }
}

/// Is `term` a quantified proposition (`For every`, `there exists`), whose
/// prose reads to the end of its sentence (§15.6)?
fn is_quantified(term: &Term) -> bool {
    match term {
        Term::Pi { .. } => true,
        Term::App { function, .. } => matches!(
            &**function,
            Term::Global(GlobalRef::Core(CoreRef::Exists | CoreRef::ExistsUnique), _)
        ),
        _ => false,
    }
}

/// Render a proposition as canonical controlled prose (§19.4). `initial`
/// selects sentence-initial capitalization; `level` is the required prose
/// level, children below it render as math islands. `trailing` says
/// whether this operand extends to the end of its enclosing proposition:
/// a quantified proposition reads to the end of the sentence (§15.6), so
/// it stands as prose only in trailing position (the right operand of a
/// connective, a body, an antecedent closed by its comma) and is a typed
/// math island elsewhere --- the same rule the source formatter applies.
#[allow(clippy::too_many_lines)]
fn prose(
    sink: &mut Sink<'_, '_>,
    term: &Term,
    initial: bool,
    level: u8,
    trailing: bool,
) -> Result<(), Diagnostic> {
    let as_prose = if is_quantified(term) {
        trailing
    } else {
        prose_level(term) >= level
    };
    if !as_prose {
        return island(sink, term, false);
    }
    match term {
        Term::Pi { binders, body } if binders.iter().all(|b| !b.spelling.is_empty()) => {
            sink.word("for", initial)?;
            sink.ws(" ");
            sink.word("every", false)?;
            for (index, binder) in binders.iter().enumerate() {
                if index > 0 {
                    sink.ws(" ");
                    sink.word("and", false)?;
                }
                sink.ws(" ");
                binder_prose(sink, binder)?;
            }
            sink.structural(",", "comma", "punctuation");
            sink.ws(" ");
            prose(sink, body, false, 0, true)?;
        }
        Term::Pi { binders, body } => {
            // Conditional: `if P, then Q` (§15.6).
            sink.word("if", initial)?;
            sink.ws(" ");
            prose(sink, &binders[0].ty, false, 1, true)?;
            sink.structural(",", "comma", "punctuation");
            sink.ws(" ");
            sink.word("then", false)?;
            sink.ws(" ");
            let rest = if binders.len() == 1 {
                (**body).clone()
            } else {
                Term::Pi {
                    binders: binders[1..].to_vec(),
                    body: body.clone(),
                }
            };
            prose(sink, &rest, false, 0, true)?;
        }
        Term::App {
            function,
            explicit_args,
            ..
        } => match &**function {
            Term::Global(GlobalRef::Core(core), _) => match (core, explicit_args.as_slice()) {
                (CoreRef::Exists | CoreRef::ExistsUnique, [Term::Lambda { binders, body }])
                    if binders.len() == 1 =>
                {
                    let unique = matches!(core, CoreRef::ExistsUnique);
                    sink.word("there", initial)?;
                    sink.ws(" ");
                    sink.word("exists", false)?;
                    sink.ws(" ");
                    if unique {
                        sink.word("exactly", false)?;
                        sink.ws(" ");
                        sink.word("one", false)?;
                        sink.ws(" ");
                    } else {
                        let article = binder_article(sink.ctx, &binders[0]);
                        sink.word(article, false)?;
                        sink.ws(" ");
                    }
                    binder_prose(sink, &binders[0])?;
                    sink.ws(" ");
                    sink.word("such", false)?;
                    sink.ws(" ");
                    sink.word("that", false)?;
                    sink.ws(" ");
                    prose(sink, body, false, 0, true)?;
                }
                (CoreRef::And, [left, right]) => {
                    prose(sink, left, initial, 4, false)?;
                    sink.ws(" ");
                    sink.word("and", false)?;
                    sink.ws(" ");
                    prose(sink, right, false, 5, trailing)?;
                }
                (CoreRef::Or, [left, right]) => {
                    prose(sink, left, initial, 3, false)?;
                    sink.ws(" ");
                    sink.word("or", false)?;
                    sink.ws(" ");
                    prose(sink, right, false, 4, trailing)?;
                }
                (CoreRef::Not, [inner]) => {
                    sink.word("not", initial)?;
                    sink.ws(" ");
                    prose(sink, inner, false, 5, trailing)?;
                }
                (CoreRef::Iff, [left, right]) => {
                    prose(sink, left, initial, 2, false)?;
                    sink.ws(" ");
                    sink.word("if", false)?;
                    sink.ws(" ");
                    sink.word("and", false)?;
                    sink.ws(" ");
                    sink.word("only", false)?;
                    sink.ws(" ");
                    sink.word("if", false)?;
                    sink.ws(" ");
                    prose(sink, right, false, 2, trailing)?;
                }
                _ => island(sink, term, false)?,
            },
            _ => atomic_prose(sink, term, initial)?,
        },
        _ => atomic_prose(sink, term, initial)?,
    }
    Ok(())
}

/// The text article for an existential binder (`a` or `an`), from the
/// binder type's canonical text form features (§13.5).
fn binder_article(ctx: &Ctx<'_>, binder: &Binder) -> &'static str {
    if let Term::Global(global, _) = &binder.ty {
        if let Some((_, entry)) = entry_for_global(ctx, global) {
            if let Some(form) = entry
                .forms
                .iter()
                .find(|form| form.canonical_source && form.channel.covers(Channel::Text))
            {
                if form.features.iter().any(|feature| feature == "article-an") {
                    return "an";
                }
            }
        }
    }
    "a"
}

/// One binder: the type's canonical text words then the local island.
fn binder_prose(sink: &mut Sink<'_, '_>, binder: &Binder) -> Result<(), Diagnostic> {
    type_prose(sink, &binder.ty)?;
    sink.ws(" ");
    sink.structural("\\(", "math-open", "control");
    sink.local(binder.id)?;
    sink.structural("\\)", "math-close", "control");
    Ok(())
}

fn period(sink: &mut Sink<'_, '_>) {
    sink.structural(".", "period", "punctuation");
}

/// The per-step source ranges of one proof in pre-order (§20.3), consumed
/// as the proof IR is walked so every proof token maps to its own step.
struct StepCursor<'a> {
    steps: &'a [(usize, usize)],
    next: usize,
}

impl StepCursor<'_> {
    fn take(&mut self) -> Result<(usize, usize), Diagnostic> {
        let range = self.steps.get(self.next).copied().ok_or_else(|| {
            Diagnostic::new(
                code!("LLI9001"),
                "phase latex: proof-step origin count does not match the proof IR",
            )
        })?;
        self.next += 1;
        Ok(range)
    }
}

/// `Case <constructor>[ with x, y]:` on its own line (module
/// documentation): the constructor through its canonical form, binders as
/// math islands.
fn case_label(
    sink: &mut Sink<'_, '_>,
    case: &crate::ir::proof::CaseProof,
) -> Result<(), Diagnostic> {
    sink.word("case-word", true)?;
    sink.ws(" ");
    let closure = sink.ctx.closure;
    let entry = closure.entry(&case.constructor).ok_or_else(|| {
        Diagnostic::new(
            code!("LLB6002"),
            format!("`{}` is unavailable", case.constructor),
        )
    })?;
    // The constructor's canonical text form when it has one, else its
    // math head as an island: an atom's math render, else its canonical
    // math surface (an operator name when it takes arguments), else the
    // qualified-ID fallback --- exactly as the constructor renders in a
    // term.
    if let Some(form_id) = text_form_id(entry) {
        sink.form_surface(&case.constructor.package, &case.constructor.entry, &form_id)?;
    } else {
        sink.structural("\\(", "math-open", "control");
        math_head(sink, &case.constructor, entry, false)?;
        sink.structural("\\)", "math-close", "control");
    }
    if !case.binders.is_empty() {
        sink.ws(" ");
        sink.word("with", false)?;
        for (index, (id, _)) in case.binders.iter().enumerate() {
            if index > 0 {
                sink.structural(",", "comma", "punctuation");
            }
            sink.ws(" ");
            sink.structural("\\(", "math-open", "control");
            sink.local(*id)?;
            sink.structural("\\)", "math-close", "control");
        }
    }
    sink.structural(":", "colon", "punctuation");
    sink.ws("\n");
    Ok(())
}

/// `Branch \(i\):` / `Premise \(i\):` on its own line.
fn numbered_label(sink: &mut Sink<'_, '_>, word: &str, index: usize) -> Result<(), Diagnostic> {
    sink.word(word, true)?;
    sink.ws(" ");
    sink.structural("\\(", "math-open", "control");
    sink.numeral(&(index + 1).to_string());
    sink.structural("\\)", "math-close", "control");
    sink.structural(":", "colon", "punctuation");
    sink.ws("\n");
    Ok(())
}

/// Canonical proof prose (§19.5).
#[allow(clippy::too_many_lines)]
fn proof_prose(
    sink: &mut Sink<'_, '_>,
    proof: &Proof,
    steps: &mut StepCursor<'_>,
) -> Result<(), Diagnostic> {
    if !matches!(proof, Proof::Sequence(_)) {
        let (start, end) = steps.take()?;
        sink.source = EmitSource::File(start, end);
    }
    match proof {
        Proof::Sequence(inner) => {
            for step in inner {
                proof_prose(sink, step, steps)?;
            }
        }
        Proof::Intro(locals) => {
            sink.word("assume", true)?;
            for (index, local) in locals.iter().enumerate() {
                if index > 0 {
                    sink.structural(",", "comma", "punctuation");
                }
                sink.ws(" ");
                sink.structural("\\(", "math-open", "control");
                sink.local(*local)?;
                sink.structural("\\)", "math-close", "control");
            }
            period(sink);
            sink.ws("\n");
        }
        Proof::Exact(term) => {
            sink.word("the", true)?;
            sink.ws(" ");
            sink.word("goal", false)?;
            sink.ws(" ");
            sink.word("follows", false)?;
            sink.ws(" ");
            sink.word("from", false)?;
            sink.ws(" ");
            island(sink, term, false)?;
            period(sink);
            sink.ws("\n");
        }
        Proof::ApplyOne(term) | Proof::Apply { function: term, .. } => {
            sink.word("apply-verb", true)?;
            sink.ws(" ");
            island(sink, term, false)?;
            period(sink);
            sink.ws("\n");
            if let Proof::Apply { premises, .. } = proof {
                let head_source = sink.source.clone();
                for (index, premise) in premises.iter().enumerate() {
                    sink.source = head_source.clone();
                    numbered_label(sink, "premise-word", index)?;
                    proof_prose(sink, premise, steps)?;
                }
            }
        }
        Proof::Reflexivity => {
            sink.word("the", true)?;
            sink.ws(" ");
            sink.word("goal", false)?;
            sink.ws(" ");
            sink.word("follows", false)?;
            sink.ws(" ");
            sink.word("by", false)?;
            sink.ws(" ");
            sink.word("reflexivity", false)?;
            period(sink);
            sink.ws("\n");
        }
        Proof::Witness(term) => {
            sink.word("use", true)?;
            sink.ws(" ");
            island(sink, term, false)?;
            sink.ws(" ");
            sink.word("as", false)?;
            sink.ws(" ");
            sink.word("the", false)?;
            sink.ws(" ");
            sink.word("witness", false)?;
            period(sink);
            sink.ws("\n");
        }
        Proof::SelectLeft | Proof::SelectRight => {
            sink.word("select", true)?;
            sink.ws(" ");
            sink.word("the", false)?;
            sink.ws(" ");
            sink.word(
                if matches!(proof, Proof::SelectLeft) {
                    "left"
                } else {
                    "right"
                },
                false,
            )?;
            sink.ws(" ");
            sink.word("alternative", false)?;
            period(sink);
            sink.ws("\n");
        }
        Proof::Have {
            proposition, proof, ..
        } => {
            sink.word("we", true)?;
            sink.ws(" ");
            sink.word("first", false)?;
            sink.ws(" ");
            sink.word("establish", false)?;
            sink.ws(" ");
            // The established proposition is prose in trailing position,
            // exactly as the source formatter spells it (§19.5, §23.5).
            prose(sink, proposition, false, 0, true)?;
            period(sink);
            sink.ws("\n");
            proof_prose(sink, proof, steps)?;
        }
        Proof::Rewrite { target, rules } => {
            sink.word("rewrite-verb", true)?;
            sink.ws(" ");
            rewrite_target_prose(sink, target)?;
            sink.ws(" ");
            sink.word("using", false)?;
            for (index, rule) in rules.iter().enumerate() {
                if index > 0 {
                    sink.structural(",", "comma", "punctuation");
                }
                sink.ws(" ");
                // Every direction stated (§19.5): a direction arrow inside
                // the island.
                sink.structural("\\(", "math-open", "control");
                sink.tok(if rule.reverse { "left-arrow" } else { "arrow" })?;
                sink.ws(" ");
                math_term(sink, &rule.term, 0)?;
                sink.structural("\\)", "math-close", "control");
            }
            period(sink);
            sink.ws("\n");
        }
        Proof::SimplifyOnly { target, rules } => {
            sink.word("simplify-verb", true)?;
            sink.ws(" ");
            rewrite_target_prose(sink, target)?;
            sink.ws(" ");
            sink.word("using", false)?;
            sink.ws(" ");
            sink.word("only", false)?;
            for (index, rule) in rules.iter().enumerate() {
                if index > 0 {
                    sink.structural(",", "comma", "punctuation");
                }
                sink.ws(" ");
                island(sink, rule, false)?;
            }
            period(sink);
            sink.ws("\n");
        }
        Proof::Constructor(branches) => {
            let head_source = sink.source.clone();
            for (index, branch) in branches.iter().enumerate() {
                sink.source = head_source.clone();
                numbered_label(sink, "branch-word", index)?;
                proof_prose(sink, branch, steps)?;
            }
        }
        Proof::Cases { scrutinee, cases } => {
            sink.word("consider", true)?;
            sink.ws(" ");
            sink.word("the", false)?;
            sink.ws(" ");
            sink.word("cases-noun", false)?;
            sink.ws(" ");
            sink.word("of", false)?;
            sink.ws(" ");
            island(sink, scrutinee, false)?;
            period(sink);
            sink.ws("\n");
            let head_source = sink.source.clone();
            for case in cases {
                sink.source = head_source.clone();
                case_label(sink, case)?;
                proof_prose(sink, &case.proof, steps)?;
            }
        }
        Proof::Induction { scrutinee, cases } => {
            sink.word("proceed", true)?;
            sink.ws(" ");
            sink.word("by", false)?;
            sink.ws(" ");
            sink.word("induction-noun", false)?;
            sink.ws(" ");
            sink.word("on", false)?;
            sink.ws(" ");
            island(sink, scrutinee, false)?;
            period(sink);
            sink.ws("\n");
            let head_source = sink.source.clone();
            for case in cases {
                sink.source = head_source.clone();
                case_label(sink, case)?;
                proof_prose(sink, &case.proof, steps)?;
            }
        }
        Proof::Calculate {
            start,
            steps: chain,
            ..
        } => {
            // A displayed aligned chain (§19.5, module documentation): one
            // `align*` row per step with the relation and justification.
            env_open(sink, "align-star")?;
            sink.ws("\n");
            math_term(sink, start, 0)?;
            for (index, step) in chain.iter().enumerate() {
                if index > 0 {
                    sink.ws(" ");
                    sink.tok("newline")?;
                    sink.ws("\n");
                }
                sink.ws(" ");
                sink.tok("align")?;
                sink.tok("equals")?;
                sink.ws(" ");
                math_term(sink, &step.term, 51)?;
                sink.ws(" ");
                sink.tok("align")?;
                sink.tok("align")?;
                sink.ws(" ");
                sink.tok("text")?;
                sink.brace(true);
                sink.word("by", false)?;
                sink.ws(" ");
                sink.brace(false);
                sink.ws(" ");
                math_term(sink, &step.proof, 0)?;
            }
            sink.ws("\n");
            env_close(sink, "align-star")?;
            sink.ws("\n");
        }
    }
    Ok(())
}

fn rewrite_target_prose(sink: &mut Sink<'_, '_>, target: &RewriteTarget) -> Result<(), Diagnostic> {
    match target {
        RewriteTarget::Goal => {
            sink.word("the", false)?;
            sink.ws(" ");
            sink.word("goal", false)?;
        }
        RewriteTarget::Hypothesis(id) => {
            sink.structural("\\(", "math-open", "control");
            sink.local(*id)?;
            sink.structural("\\)", "math-close", "control");
        }
    }
    Ok(())
}

/// Whether one space separates two adjacent phrase items (§15.3): none
/// before `:` or `)`, none after `(`, and a hyphen is tight on both sides.
fn phrase_space(previous: &PhraseItem, next: &PhraseItem) -> bool {
    let punct = |item: &PhraseItem| match item {
        PhraseItem::Punctuation(entry) => Some(entry.entry.clone()),
        _ => None,
    };
    !matches!(
        (punct(previous).as_deref(), punct(next).as_deref()),
        (Some("paren-open" | "hyphen"), _) | (_, Some("colon" | "paren-close" | "hyphen"))
    )
}

fn phrase_prose(sink: &mut Sink<'_, '_>, phrase: &Phrase) -> Result<(), Diagnostic> {
    for (index, item) in phrase.items.iter().enumerate() {
        if index > 0 && phrase_space(&phrase.items[index - 1], item) {
            sink.ws(" ");
        }
        match item {
            PhraseItem::Word { entry, form } => {
                sink.form_surface(&entry.package, &entry.entry, form)?;
            }
            PhraseItem::Math(term) => term_phrase(sink, term, false)?,
            PhraseItem::Punctuation(entry) => {
                let text = match entry.entry.as_str() {
                    "colon" => ":",
                    "hyphen" => "-",
                    "paren-open" => "(",
                    "paren-close" => ")",
                    other => {
                        return Err(Diagnostic::new(
                            code!("LLB6002"),
                            format!("`{other}` is not phrase punctuation"),
                        ))
                    }
                };
                sink.structural(text, &entry.entry, "punctuation");
            }
        }
    }
    Ok(())
}

/// The label slug: the module name lowercased with `.` as `-` (§19.3).
#[must_use]
pub fn module_slug(module: &str) -> String {
    module.to_lowercase().replace('.', "-")
}

fn env_open(sink: &mut Sink<'_, '_>, env_token: &str) -> Result<(), Diagnostic> {
    sink.tok("begin")?;
    sink.brace(true);
    sink.tok(env_token)?;
    sink.brace(false);
    Ok(())
}

fn env_close(sink: &mut Sink<'_, '_>, env_token: &str) -> Result<(), Diagnostic> {
    sink.tok("end")?;
    sink.brace(true);
    sink.tok(env_token)?;
    sink.brace(false);
    Ok(())
}

fn label(sink: &mut Sink<'_, '_>, module: &str, component: &str) -> Result<(), Diagnostic> {
    sink.tok("label")?;
    sink.brace(true);
    sink.metadata(
        &format!("ll:{}:{component}", module_slug(module)),
        &format!("{module}::{component}"),
    );
    sink.brace(false);
    Ok(())
}

/// Render one module's canonical `.tex` (§19.2, §19.3).
#[allow(clippy::too_many_lines)]
pub fn render_module(checked: &CheckedModule, closure: &Closure) -> Result<Emitter, Diagnostic> {
    let document = &checked.document;
    let mut spellings = BTreeMap::new();
    collect_spellings_document(document, &mut spellings);
    for (id, spelling) in &checked.proof_spellings {
        spellings.entry(*id).or_insert_with(|| spelling.clone());
    }
    let ctx = Ctx::new(closure, &checked.visible, spellings);
    let mut emitter = Emitter::new();
    let preamble_node = emitter.node("latex-preamble");
    {
        let mut sink = Sink {
            emitter: &mut emitter,
            ctx: &ctx,
            source: EmitSource::Synthetic("core:latex-preamble/1".to_owned()),
            role: MapRole::Synthetic,
            node: preamble_node,
        };
        // The exact preamble (§19.2).
        sink.tok("documentclass")?;
        sink.tok("left-bracket")?;
        sink.tok("opt-11pt")?;
        sink.tok("right-bracket")?;
        sink.brace(true);
        sink.tok("article")?;
        sink.brace(false);
        sink.ws("\n");
        sink.tok("usepackage")?;
        sink.tok("left-bracket")?;
        sink.tok("opt-t1")?;
        sink.tok("right-bracket")?;
        sink.brace(true);
        sink.tok("fontenc")?;
        sink.brace(false);
        sink.ws("\n");
        for package in ["amsmath", "amssymb", "amsthm"] {
            sink.tok("usepackage")?;
            sink.brace(true);
            sink.tok(package)?;
            sink.brace(false);
            sink.ws("\n");
        }
        sink.tok("usepackage")?;
        sink.tok("left-bracket")?;
        sink.tok("hidelinks")?;
        sink.tok("right-bracket")?;
        sink.brace(true);
        sink.tok("hyperref")?;
        sink.brace(false);
        sink.ws("\n");
        sink.tok("newtheorem")?;
        sink.brace(true);
        sink.tok("theorem")?;
        sink.brace(false);
        sink.brace(true);
        sink.tok("theorem-title")?;
        sink.brace(false);
        sink.tok("left-bracket")?;
        sink.tok("section-counter")?;
        sink.tok("right-bracket")?;
        sink.ws("\n");
        for (env, title) in [("lemma", "lemma-title"), ("corollary", "corollary-title")] {
            sink.tok("newtheorem")?;
            sink.brace(true);
            sink.tok(env)?;
            sink.brace(false);
            sink.tok("left-bracket")?;
            sink.tok("theorem")?;
            sink.tok("right-bracket")?;
            sink.brace(true);
            sink.tok(title)?;
            sink.brace(false);
            sink.ws("\n");
        }
        sink.tok("theoremstyle")?;
        sink.brace(true);
        sink.tok("definition")?;
        sink.brace(false);
        sink.ws("\n");
        sink.tok("newtheorem")?;
        sink.brace(true);
        sink.tok("definition")?;
        sink.brace(false);
        sink.tok("left-bracket")?;
        sink.tok("theorem")?;
        sink.tok("right-bracket")?;
        sink.brace(true);
        sink.tok("definition-title")?;
        sink.brace(false);
        sink.ws("\n");
        sink.tok("begin")?;
        sink.brace(true);
        sink.tok("document")?;
        sink.brace(false);
        sink.ws("\n");
    }

    // The title (§19.3): a center environment with \LARGE.
    let title_node = emitter.node("title");
    {
        let mut sink = Sink {
            emitter: &mut emitter,
            ctx: &ctx,
            source: EmitSource::Synthetic("core:latex-structure/1".to_owned()),
            role: MapRole::Structure,
            node: title_node,
        };
        env_open(&mut sink, "center")?;
        sink.ws("\n");
        sink.brace(true);
        sink.tok("large")?;
        sink.ws(" ");
        phrase_prose(&mut sink, &document.title)?;
        sink.brace(false);
        sink.ws("\n");
        env_close(&mut sink, "center")?;
        sink.ws("\n");
    }

    render_blocks(&mut emitter, &ctx, checked, &document.blocks, 0)?;

    let end_node = emitter.node("latex-preamble");
    {
        let mut sink = Sink {
            emitter: &mut emitter,
            ctx: &ctx,
            source: EmitSource::Synthetic("core:latex-preamble/1".to_owned()),
            role: MapRole::Synthetic,
            node: end_node,
        };
        sink.tok("end")?;
        sink.brace(true);
        sink.tok("document")?;
        sink.brace(false);
        sink.ws("\n");
    }
    Ok(emitter)
}

#[allow(clippy::too_many_lines)]
fn render_blocks(
    emitter: &mut Emitter,
    ctx: &Ctx<'_>,
    checked: &CheckedModule,
    blocks: &[Block],
    depth: usize,
) -> Result<(), Diagnostic> {
    let document = &checked.document;
    for block in blocks {
        match block {
            Block::Section(section) => {
                let node = emitter.node("section");
                let mut sink = Sink {
                    emitter,
                    ctx,
                    source: EmitSource::Synthetic("core:latex-structure/1".to_owned()),
                    role: MapRole::Structure,
                    node,
                };
                match depth {
                    0 => sink.tok("section")?,
                    1 => sink.tok("subsection")?,
                    _ => {
                        // The deterministic bold heading construct beyond
                        // two levels (§19.3, module documentation).
                        sink.tok("textbf")?;
                    }
                }
                sink.brace(true);
                phrase_prose(&mut sink, &section.heading)?;
                sink.brace(false);
                sink.ws("\n");
                label(&mut sink, &document.name, &section.component)?;
                sink.ws("\n");
                if !section.params.is_empty() {
                    // The parameters display (§19.3): labeled by the core
                    // concept `Parameters`.
                    sink.structural("\\[", "display-open", "control");
                    sink.tok("mathrm")?;
                    sink.brace(true);
                    sink.form_surface("lexlean.core", "parameters-concept", "parameters")?;
                    sink.brace(false);
                    sink.tok("colon")?;
                    for (index, binder) in section.params.iter().enumerate() {
                        if index > 0 {
                            sink.tok("semicolon")?;
                        }
                        sink.ws(" ");
                        sink.tok("forall")?;
                        sink.ws(" ");
                        sink.local(binder.id)?;
                        sink.ws(" ");
                        sink.tok("member")?;
                        sink.ws(" ");
                        math_term(&mut sink, &binder.ty, 255)?;
                    }
                    sink.structural("\\]", "display-close", "control");
                    sink.ws("\n");
                }
                render_blocks(emitter, ctx, checked, &section.blocks, depth + 1)?;
            }
            Block::Declaration(declaration) => {
                render_declaration(emitter, ctx, checked, declaration)?;
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn render_declaration(
    emitter: &mut Emitter,
    ctx: &Ctx<'_>,
    checked: &CheckedModule,
    declaration: &Declaration,
) -> Result<(), Diagnostic> {
    let document = &checked.document;
    // No declaration renders without its source ranges (§20.3 forbids a
    // fabricated span).
    let origin: &DeclOrigin = checked
        .decl_origins
        .get(&declaration.component)
        .ok_or_else(|| {
            Diagnostic::new(
                code!("LLI9001"),
                format!(
                    "phase latex: declaration `{}` has no source origin",
                    declaration.component
                ),
            )
        })?;
    let node = emitter.node("declaration");
    let env_token = match declaration.kind {
        DeclKind::Theorem => "theorem",
        DeclKind::Lemma => "lemma",
        DeclKind::Corollary => "corollary",
        _ => "definition",
    };
    {
        let mut sink = Sink {
            emitter,
            ctx,
            source: EmitSource::File(origin.whole.0, origin.whole.1),
            role: MapRole::Structure,
            node,
        };
        env_open(&mut sink, env_token)?;
        sink.ws("\n");
        label(&mut sink, &document.name, &declaration.component)?;
        sink.ws("\n");
        sink.source = EmitSource::File(origin.sentence.0, origin.sentence.1);
        sink.role = MapRole::Term;
        match &declaration.body {
            DeclBody::TheoremLike { statement, .. } => {
                prose(&mut sink, statement, true, 0, true)?;
                period(&mut sink);
                sink.ws("\n");
            }
            DeclBody::Definition { entry, ty, value } => {
                definition_prose(&mut sink, declaration, entry, ty, value)?;
                sink.ws("\n");
            }
        }
        env_close(&mut sink, env_token)?;
        sink.ws("\n");
    }
    if let DeclBody::TheoremLike { proof, .. } = &declaration.body {
        let proof_node = emitter.node("proof");
        let mut sink = Sink {
            emitter,
            ctx,
            source: match origin.proof {
                Some((start, end)) => EmitSource::File(start, end),
                None => EmitSource::File(origin.whole.0, origin.whole.1),
            },
            role: MapRole::Proof,
            node: proof_node,
        };
        env_open(&mut sink, "proof")?;
        sink.ws("\n");
        let mut cursor = StepCursor {
            steps: &origin.steps,
            next: 0,
        };
        proof_prose(&mut sink, proof, &mut cursor)?;
        if cursor.next != cursor.steps.len() {
            return Err(Diagnostic::new(
                code!("LLI9001"),
                format!(
                    "phase latex: declaration `{}` has {} proof-step origins for {} rendered steps",
                    declaration.component,
                    cursor.steps.len(),
                    cursor.next
                ),
            ));
        }
        sink.source = match origin.proof {
            Some((start, end)) => EmitSource::File(start, end),
            None => EmitSource::File(origin.whole.0, origin.whole.1),
        };
        env_close(&mut sink, "proof")?;
        sink.ws("\n");
    }
    Ok(())
}

fn definition_prose(
    sink: &mut Sink<'_, '_>,
    declaration: &Declaration,
    entry: &QualifiedId,
    ty: &Term,
    value: &Term,
) -> Result<(), Diagnostic> {
    let closure = sink.ctx.closure;
    let glossary_entry = closure
        .entry(entry)
        .ok_or_else(|| Diagnostic::new(code!("LLB6002"), format!("`{entry}` is unavailable")))?;
    let (binders, rhs) = match value {
        Term::Lambda { binders, body } => (binders.clone(), (**body).clone()),
        other => (Vec::new(), other.clone()),
    };
    let mut initial = true;
    if !binders.is_empty() {
        sink.word("for", true)?;
        sink.ws(" ");
        sink.word("every", false)?;
        for (index, binder) in binders.iter().enumerate() {
            if index > 0 {
                sink.ws(" ");
                sink.word("and", false)?;
            }
            sink.ws(" ");
            binder_prose(sink, binder)?;
        }
        sink.structural(",", "comma", "punctuation");
        sink.ws(" ");
        initial = false;
    }
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
                })
                .unwrap_or_else(|| "article-a".to_owned());
            sink.word(if article == "article-an" { "an" } else { "a" }, initial)?;
            sink.ws(" ");
            text_frame(sink, entry, glossary_entry, &[], false)?;
            sink.ws(" ");
            for word in ["is", "defined", "as"] {
                sink.word(word, false)?;
                sink.ws(" ");
            }
            island(sink, &rhs, false)?;
            period(sink);
        }
        DeclKind::TermDefinition => {
            self_head_prose(sink, entry, glossary_entry, &binders, initial)?;
            sink.ws(" ");
            for word in ["is", "defined", "as"] {
                sink.word(word, false)?;
                sink.ws(" ");
            }
            island(sink, &rhs, false)?;
            period(sink);
        }
        DeclKind::PredicateDefinition => {
            self_head_prose(sink, entry, glossary_entry, &binders, initial)?;
            sink.ws(" ");
            for word in ["holds", "exactly", "when"] {
                sink.word(word, false)?;
                sink.ws(" ");
            }
            prose(sink, &rhs, false, 0, true)?;
            period(sink);
        }
        _ => {
            return Err(Diagnostic::new(
                code!("LLI9001"),
                "phase latex: theorem-like kind in definition prose",
            ));
        }
    }
    let _ = ty;
    Ok(())
}

/// The definition self head (§15.7 rule 4): the entry's text frame over
/// its signature binders when the entry is text-canonical, otherwise a
/// self application island through the entry's math render.
fn self_head_prose(
    sink: &mut Sink<'_, '_>,
    entry_id: &QualifiedId,
    entry: &Entry,
    binders: &[Binder],
    initial: bool,
) -> Result<(), Diagnostic> {
    if TEXT_FRAMES.contains(&entry.frame)
        && entry.surface_arity as usize == binders.len()
        && text_form_id(entry).is_some()
    {
        let args: Vec<Term> = binders
            .iter()
            .map(|binder| Term::Local(binder.id))
            .collect();
        return text_frame(sink, entry_id, entry, &args, initial);
    }
    // A self application island through the entry's math render.
    sink.structural("\\(", "math-open", "control");
    if let Some(render) = entry.render_math.clone() {
        let args: Vec<(Term, u8)> = binders
            .iter()
            .map(|binder| {
                (
                    Term::Local(binder.id),
                    entry.precedence.map_or(0, |p| p + 1),
                )
            })
            .collect();
        eval_lre(sink, &render, entry_id, &args)?;
    } else {
        fallback_qualified(sink, entry_id)?;
    }
    sink.structural("\\)", "math-close", "control");
    Ok(())
}

/// Collect display spellings from a document, public for the formatter.
pub fn collect_spellings_public(document: &DocumentModule, out: &mut BTreeMap<LocalId, String>) {
    collect_spellings_document(document, out);
}

fn collect_spellings_document(document: &DocumentModule, out: &mut BTreeMap<LocalId, String>) {
    fn term_spellings(term: &Term, out: &mut BTreeMap<LocalId, String>) {
        match term {
            Term::Pi { binders, body } | Term::Lambda { binders, body } => {
                for binder in binders {
                    if !binder.spelling.is_empty() {
                        out.insert(binder.id, binder.spelling.clone());
                    }
                    term_spellings(&binder.ty, out);
                }
                term_spellings(body, out);
            }
            Term::Let {
                binder,
                value,
                body,
            } => {
                if !binder.spelling.is_empty() {
                    out.insert(binder.id, binder.spelling.clone());
                }
                term_spellings(&binder.ty, out);
                term_spellings(value, out);
                term_spellings(body, out);
            }
            Term::App {
                function,
                explicit_args,
                ..
            } => {
                term_spellings(function, out);
                for argument in explicit_args {
                    term_spellings(argument, out);
                }
            }
            Term::NatLiteral { expected_type, .. } => term_spellings(expected_type, out),
            _ => {}
        }
    }
    fn proof_spellings(proof: &Proof, out: &mut BTreeMap<LocalId, String>) {
        match proof {
            Proof::Sequence(steps) => steps.iter().for_each(|step| proof_spellings(step, out)),
            Proof::Exact(term) | Proof::ApplyOne(term) | Proof::Witness(term) => {
                term_spellings(term, out);
            }
            Proof::Apply { function, premises } => {
                term_spellings(function, out);
                premises
                    .iter()
                    .for_each(|premise| proof_spellings(premise, out));
            }
            Proof::Have {
                proposition, proof, ..
            } => {
                term_spellings(proposition, out);
                proof_spellings(proof, out);
            }
            Proof::Rewrite { rules, .. } => rules
                .iter()
                .for_each(|rule| term_spellings(&rule.term, out)),
            Proof::SimplifyOnly { rules, .. } => {
                rules.iter().for_each(|rule| term_spellings(rule, out));
            }
            Proof::Constructor(branches) => {
                branches
                    .iter()
                    .for_each(|branch| proof_spellings(branch, out));
            }
            Proof::Cases { scrutinee, cases } | Proof::Induction { scrutinee, cases } => {
                term_spellings(scrutinee, out);
                for case in cases {
                    for (id, spelling) in &case.binders {
                        out.insert(*id, spelling.clone());
                    }
                    proof_spellings(&case.proof, out);
                }
            }
            Proof::Calculate { start, steps, .. } => {
                term_spellings(start, out);
                for step in steps {
                    term_spellings(&step.term, out);
                    term_spellings(&step.proof, out);
                }
            }
            _ => {}
        }
    }
    fn block_spellings(block: &Block, out: &mut BTreeMap<LocalId, String>) {
        match block {
            Block::Section(section) => {
                for binder in &section.params {
                    if !binder.spelling.is_empty() {
                        out.insert(binder.id, binder.spelling.clone());
                    }
                    term_spellings(&binder.ty, out);
                }
                section
                    .blocks
                    .iter()
                    .for_each(|inner| block_spellings(inner, out));
            }
            Block::Declaration(declaration) => {
                for binder in &declaration.params {
                    if !binder.spelling.is_empty() {
                        out.insert(binder.id, binder.spelling.clone());
                    }
                }
                match &declaration.body {
                    DeclBody::TheoremLike { statement, proof } => {
                        term_spellings(statement, out);
                        proof_spellings(proof, out);
                    }
                    DeclBody::Definition { ty, value, .. } => {
                        term_spellings(ty, out);
                        term_spellings(value, out);
                    }
                }
            }
        }
    }
    for item in &document.title.items {
        if let PhraseItem::Math(term) = item {
            term_spellings(term, out);
        }
    }
    document
        .blocks
        .iter()
        .for_each(|block| block_spellings(block, out));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::artifact::content_id::Sha256Digest;
    use crate::ir::term::{DocumentDeclRef, ExternalConstRef, Universe};
    use crate::lexicon::lse::BinderMode;
    use crate::lexicon::package::LoadContext;
    use crate::lexicon::{load_bootstrap, load_builtin_package, load_token_registry};

    /// The built-in closure (`lexlean.core`, `lexlean.std.nat`).
    fn closure() -> Closure {
        let bootstrap = load_bootstrap().expect("bootstrap loads");
        let ctx = LoadContext {
            forbidden_controls: &bootstrap.structural.forbidden_controls,
            max_scope_depth: 1024,
        };
        let packages = bootstrap
            .builtin_packages
            .iter()
            .map(|row| load_builtin_package(row, &ctx).expect("builtin package loads"))
            .collect();
        let registry = load_token_registry().expect("registry loads");
        Closure::build(packages, registry, bootstrap, 128).expect("closure")
    }

    fn external(entry: &str, lean_name: &str) -> Term {
        Term::Global(
            GlobalRef::External(ExternalConstRef {
                package: "lexlean.std.nat@1.0.0".to_owned(),
                entry: format!("lexlean.std.nat::{entry}"),
                lean_module: "Init".to_owned(),
                lean_name: lean_name.to_owned(),
                signature_hash: Sha256Digest::of(entry.as_bytes()),
            }),
            Vec::new(),
        )
    }

    fn nat() -> Term {
        external("nat", "Nat")
    }

    fn binder(id: u64, spelling: &str, ty: Term) -> Binder {
        Binder {
            id: LocalId(id),
            mode: BinderMode::Explicit,
            ty,
            spelling: spelling.to_owned(),
        }
    }

    fn app(function: Term, args: Vec<Term>) -> Term {
        Term::App {
            function: Box::new(function),
            explicit_args: args,
            omitted_implicit_binders: Vec::new(),
        }
    }

    fn core(core: CoreRef) -> Term {
        Term::Global(GlobalRef::Core(core), Vec::new())
    }

    fn eq(left: Term, right: Term) -> Term {
        app(core(CoreRef::Eq), vec![left, right])
    }

    fn exists(binder: Binder, body: Term) -> Term {
        app(
            core(CoreRef::Exists),
            vec![Term::Lambda {
                binders: vec![binder],
                body: Box::new(body),
            }],
        )
    }

    fn reference(component: &str) -> Term {
        Term::Global(
            GlobalRef::Document(DocumentDeclRef {
                module: "Main".to_owned(),
                component: component.to_owned(),
                lean_name: format!("LexLeanExample.Main.{}", component.replace('-', "_")),
            }),
            Vec::new(),
        )
    }

    /// Render through `render` (math or prose) with the given local
    /// spellings; returns the bytes and their coverage origins.
    fn render(
        spellings: &[(u64, &str)],
        render: impl FnOnce(&mut Sink<'_, '_>) -> Result<(), Diagnostic>,
    ) -> Result<(String, Vec<Origin>), Diagnostic> {
        let closure = closure();
        let visible = closure.visible_set(&["lexlean.std.nat".to_owned()]);
        let ctx = Ctx::new(
            &closure,
            &visible,
            spellings
                .iter()
                .map(|(id, spelling)| (LocalId(*id), (*spelling).to_owned()))
                .collect(),
        );
        let mut emitter = Emitter::new();
        let node = emitter.node("test");
        let mut sink = Sink {
            emitter: &mut emitter,
            ctx: &ctx,
            source: EmitSource::Synthetic("test".to_owned()),
            role: MapRole::Structure,
            node,
        };
        render(&mut sink)?;
        let origins = emitter
            .coverage_rows()
            .into_iter()
            .map(|row| row.origin)
            .collect();
        Ok((emitter.text().to_owned(), origins))
    }

    #[test]
    fn document_references_render_by_reference_origin() {
        // Unapplied and applied alike: `\texttt{Module::component}` under
        // `Origin::Reference`, never the Lean name's `_` in math.
        let expected_origin = Origin::Reference {
            module: "Main".to_owned(),
            component: "zero-add".to_owned(),
        };
        let (text, origins) = render(&[(0, "n")], |sink| {
            math_term(sink, &reference("zero-add"), 0)
        })
        .expect("renders");
        assert_eq!(text, "\\texttt{Main::zero-add}");
        assert!(origins.contains(&expected_origin));
        assert!(!origins
            .iter()
            .any(|origin| matches!(origin, Origin::Metadata { .. })));
        let applied = app(reference("zero-add"), vec![Term::Local(LocalId(0))]);
        let (text, origins) =
            render(&[(0, "n")], |sink| math_term(sink, &applied, 0)).expect("renders");
        assert_eq!(text, "\\texttt{Main::zero-add}(n)");
        assert!(origins.contains(&expected_origin));
    }

    #[test]
    fn quantifier_islands_state_binder_types() {
        let m = Term::Local(LocalId(1));
        let n = Term::Local(LocalId(0));
        let existential = exists(binder(1, "m", nat()), eq(n.clone(), m.clone()));
        let (text, _) = render(&[(0, "n"), (1, "m")], |sink| {
            math_term(sink, &existential, 0)
        })
        .expect("renders");
        assert_eq!(text, "\\exists m \\in \\mathbb{N}, n = m");
        let universal = Term::Pi {
            binders: vec![binder(0, "n", nat()), binder(1, "m", nat())],
            body: Box::new(eq(n.clone(), m.clone())),
        };
        let (text, _) =
            render(&[(0, "n"), (1, "m")], |sink| math_term(sink, &universal, 0)).expect("renders");
        assert_eq!(
            text,
            "\\forall n \\in \\mathbb{N}, \\forall m \\in \\mathbb{N}, n = m"
        );
        // A quantifier followed by anonymous binders is the quantified
        // implication; a right-nested implication takes no parentheses.
        let mixed = Term::Pi {
            binders: vec![
                binder(0, "n", nat()),
                binder(2, "", eq(n.clone(), n.clone())),
                binder(3, "", eq(m.clone(), m.clone())),
            ],
            body: Box::new(eq(n.clone(), m.clone())),
        };
        let (text, _) =
            render(&[(0, "n"), (1, "m")], |sink| math_term(sink, &mixed, 0)).expect("renders");
        assert_eq!(
            text,
            "\\forall n \\in \\mathbb{N}, n = n \\to m = m \\to n = m"
        );
        // An implication as the antecedent of an implication is
        // parenthesized (right associativity, §13.10).
        let nested = Term::Pi {
            binders: vec![binder(
                2,
                "",
                Term::Pi {
                    binders: vec![binder(3, "", eq(n.clone(), n.clone()))],
                    body: Box::new(eq(m.clone(), m.clone())),
                },
            )],
            body: Box::new(eq(n, m)),
        };
        let (text, _) =
            render(&[(0, "n"), (1, "m")], |sink| math_term(sink, &nested, 0)).expect("renders");
        assert_eq!(text, "(n = n \\to m = m) \\to n = m");
    }

    #[test]
    fn quantified_operands_are_prose_only_in_trailing_position() {
        let n = Term::Local(LocalId(0));
        let m = Term::Local(LocalId(1));
        let existential = exists(binder(1, "m", nat()), eq(n.clone(), m.clone()));
        let zero = Term::NatLiteral {
            decimal: "0".to_owned(),
            expected_type: Box::new(nat()),
        };
        // Right operand: trailing, so prose (the source spelling).
        let right = app(
            core(CoreRef::Or),
            vec![eq(n.clone(), zero.clone()), existential.clone()],
        );
        let (text, _) = render(&[(0, "n"), (1, "m")], |sink| {
            prose(sink, &right, true, 0, true)
        })
        .expect("renders");
        assert_eq!(
            text,
            "\\(n = 0\\) or there exists a natural number \\(m\\) such that \\(n = m\\)"
        );
        // Left operand: not trailing, so a typed island.
        let left = app(core(CoreRef::Or), vec![existential, eq(n, zero)]);
        let (text, _) = render(&[(0, "n"), (1, "m")], |sink| {
            prose(sink, &left, true, 0, true)
        })
        .expect("renders");
        assert_eq!(
            text,
            "\\(\\exists m \\in \\mathbb{N}, n = m\\) or \\(n = 0\\)"
        );
    }

    #[test]
    fn sorts_state_numeric_levels_and_refuse_symbolic_ones() {
        for (universe, expected) in [
            (Universe::Num(0), "\\mathrm{Prop}"),
            (Universe::Num(1), "\\mathrm{Type}"),
            (Universe::Num(2), "\\mathrm{Type}_{1}"),
            (Universe::Num(4), "\\mathrm{Type}_{3}"),
        ] {
            let (text, _) =
                render(&[], |sink| math_term(sink, &Term::Sort(universe), 0)).expect("renders");
            assert_eq!(text, expected);
        }
        let error = render(&[], |sink| {
            math_term(sink, &Term::Sort(Universe::Var("u".to_owned())), 0)
        })
        .expect_err("a symbolic level has no canonical rendering");
        assert_eq!(error.code.as_str(), "LLB6002");
        assert!(error.message.contains("symbolic universe level"));
    }

    #[test]
    fn saturated_atoms_and_operator_heads() {
        // An application with no explicit arguments renders as its atom;
        // an unapplied or arity-mismatched operator head is an operator
        // name and atomic (no parentheses at any minimum precedence).
        let (text, _) =
            render(&[], |sink| math_term(sink, &app(nat(), Vec::new()), 0)).expect("renders");
        assert_eq!(text, "\\mathbb{N}");
        let succ = external("succ", "Nat.succ");
        let (text, _) = render(&[], |sink| math_term(sink, &succ, 0)).expect("renders");
        assert_eq!(text, "\\operatorname{succ}");
        let over_applied = app(succ, vec![Term::Local(LocalId(0)), Term::Local(LocalId(0))]);
        let (text, _) =
            render(&[(0, "n")], |sink| math_term(sink, &over_applied, 255)).expect("renders");
        assert_eq!(text, "\\operatorname{succ}(n, n)");
    }
}
