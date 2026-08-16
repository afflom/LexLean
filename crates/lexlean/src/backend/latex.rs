//! The canonical LaTeX backend (SPEC.md §19): rendered solely from linked
//! IR, never copied from source (I8). Every visible word comes from a
//! canonical glossary form, every mathematical construct from LRE and the
//! renderer-token registry, and every structural control from the fixed
//! backend, with complete output coverage (§19.6).

use std::collections::BTreeMap;

use crate::artifact::source_map::MapRole;
use crate::backend::{EmitSource, Emitter};
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::ir::declaration::{DeclBody, DeclKind, Declaration};
use crate::ir::document::{Block, DocumentModule, Phrase, PhraseItem};
use crate::ir::proof::{Proof, RewriteTarget};
use crate::ir::term::{Binder, CoreRef, GlobalRef, LocalId, Term};
use crate::lexicon::entry::{Channel, Entry};
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
        self.emitter.piece(
            &bytes,
            kind,
            Origin::RendererToken(id.to_owned()),
            self.source.clone(),
            self.role,
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
        self.emitter.piece(
            text,
            kind,
            Origin::Structural {
                package: "lexlean.core".to_owned(),
                entry: entry.to_owned(),
            },
            self.source.clone(),
            self.role,
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

    fn local(&mut self, id: LocalId) {
        let spelling = self
            .ctx
            .spellings
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("x{}", id.0));
        self.emitter.piece(
            &spelling,
            "word",
            Origin::Local(id.0 as usize),
            self.source.clone(),
            self.role,
            self.node,
        );
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

    fn ws(&mut self, text: &str) {
        self.emitter.ws(text);
    }
}

/// The canonical math entry for a global, for LRE-driven rendering.
fn entry_for_global<'c>(
    closure: &'c Closure,
    global: &GlobalRef,
) -> Option<(QualifiedId, &'c Entry)> {
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
    let entry = closure.entry(&qualified)?;
    Some((qualified, entry))
}

/// The top-level operator precedence of a term for parenthesization, 255
/// for atoms.
fn term_prec(closure: &Closure, term: &Term) -> u8 {
    match term {
        Term::App { function, .. } => match &**function {
            Term::Global(global, _) => entry_for_global(closure, global)
                .and_then(|(_, entry)| entry.precedence)
                .unwrap_or(255),
            _ => 255,
        },
        Term::Pi { .. } | Term::Lambda { .. } => 10,
        _ => 255,
    }
}

#[allow(clippy::too_many_lines)]
fn math_term(sink: &mut Sink<'_, '_>, term: &Term, min_prec: u8) -> Result<(), Diagnostic> {
    let closure = sink.ctx.closure;
    let own_prec = term_prec(closure, term);
    let needs_parens = own_prec < min_prec;
    if needs_parens {
        sink.tok("left-paren")?;
    }
    match term {
        Term::Local(id) => sink.local(*id),
        Term::NatLiteral { decimal, .. } => sink.numeral(decimal),
        Term::Sort(universe) => {
            sink.tok("mathrm")?;
            sink.brace(true);
            let name = match universe {
                crate::ir::term::Universe::Num(0) => "Prop",
                _ => "Type",
            };
            sink.metadata(name, "core:lean-syntax/1");
            sink.brace(false);
        }
        Term::Global(global, _) => match entry_for_global(closure, global) {
            Some((qualified, entry)) => {
                if let Some(render) = entry.render_math.clone() {
                    if entry.surface_arity == 0 {
                        eval_lre(sink, &render, &qualified, &[])?;
                    } else {
                        fallback_qualified(sink, &qualified)?;
                    }
                } else if let Some(form) = entry
                    .forms
                    .iter()
                    .find(|form| form.canonical_source && form.channel.covers(Channel::Math))
                {
                    let form_id = form.id.clone();
                    sink.form_surface(&qualified.package, &qualified.entry, &form_id)?;
                } else {
                    fallback_qualified(sink, &qualified)?;
                }
            }
            None => fallback_global(sink, global)?,
        },
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
                    sink.tok(if unique { "exists-unique" } else { "exists" })?;
                    if let Term::Lambda { binders, body } = &explicit_args[0] {
                        for binder in binders {
                            sink.ws(" ");
                            sink.local(binder.id);
                        }
                        sink.tok("comma")?;
                        sink.ws(" ");
                        math_term(sink, body, 0)?;
                    } else {
                        sink.ws(" ");
                        math_term(sink, &explicit_args[0], 255)?;
                    }
                }
                _ => match entry_for_global(closure, global) {
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
                                            _ => op + 1,
                                        };
                                        let right_min = match assoc {
                                            Associativity::Right => op,
                                            _ => op + 1,
                                        };
                                        if index == 0 {
                                            left_min
                                        } else {
                                            right_min
                                        }
                                    }
                                    (Some(op), None) => op + 1,
                                    _ => 0,
                                };
                                (argument.clone(), required)
                            })
                            .collect();
                        eval_lre(sink, &render, &qualified, &arg_specs)?;
                    }
                    _ => {
                        // Fallback: qualified head with a parenthesized
                        // argument list.
                        match global {
                            GlobalRef::Document(document) => {
                                sink.tok("operatorname")?;
                                sink.brace(true);
                                let short = document
                                    .lean_name
                                    .rsplit('.')
                                    .next()
                                    .unwrap_or(&document.lean_name)
                                    .to_owned();
                                sink.metadata(
                                    &short,
                                    &format!("{}::{}", document.module, document.component),
                                );
                                sink.brace(false);
                            }
                            other => fallback_global(sink, other)?,
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
            if binders.iter().all(|binder| binder.spelling.is_empty()) {
                // Implication: the core arrow with `\to` (§13.10).
                math_term(sink, &binders[0].ty, 26)?;
                sink.ws(" ");
                sink.tok("implies")?;
                sink.ws(" ");
                let rest = if binders.len() == 1 {
                    (**body).clone()
                } else {
                    Term::Pi {
                        binders: binders[1..].to_vec(),
                        body: body.clone(),
                    }
                };
                math_term(sink, &rest, 25)?;
            } else {
                sink.tok("forall")?;
                for binder in binders {
                    sink.ws(" ");
                    sink.local(binder.id);
                }
                sink.tok("comma")?;
                sink.ws(" ");
                math_term(sink, body, 0)?;
            }
        }
        Term::Lambda { binders, body } => {
            for binder in binders {
                sink.local(binder.id);
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
            sink.tok("texttt")?;
            sink.brace(true);
            sink.metadata(
                &format!("{}::{}", document.module, document.component),
                &format!("{}::{}", document.module, document.component),
            );
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
        Render::Sub(..) | Render::Sup(..) | Render::Frac(..) => {
            return Err(Diagnostic::new(
                code!("LLB6002"),
                "sub, sup, and frac renders need registry rows the language-1.0 registry does not carry",
            ));
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

/// Render a proposition as canonical controlled prose (§19.4). `initial`
/// selects sentence-initial capitalization; `level` is the required prose
/// level, children below it render as math islands.
#[allow(clippy::too_many_lines)]
fn prose(sink: &mut Sink<'_, '_>, term: &Term, initial: bool, level: u8) -> Result<(), Diagnostic> {
    if prose_level(term) < level {
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
            prose(sink, body, false, 0)?;
        }
        Term::Pi { binders, body } => {
            // Conditional: `if P, then Q` (§15.6).
            sink.word("if", initial)?;
            sink.ws(" ");
            prose(sink, &binders[0].ty, false, 1)?;
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
            prose(sink, &rest, false, 0)?;
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
                        let article = binder_article(sink.ctx.closure, &binders[0]);
                        sink.word(article, false)?;
                        sink.ws(" ");
                    }
                    binder_prose(sink, &binders[0])?;
                    sink.ws(" ");
                    sink.word("such", false)?;
                    sink.ws(" ");
                    sink.word("that", false)?;
                    sink.ws(" ");
                    prose(sink, body, false, 0)?;
                }
                (CoreRef::And, [left, right]) => {
                    prose(sink, left, initial, 4)?;
                    sink.ws(" ");
                    sink.word("and", false)?;
                    sink.ws(" ");
                    prose(sink, right, false, 5)?;
                }
                (CoreRef::Or, [left, right]) => {
                    prose(sink, left, initial, 3)?;
                    sink.ws(" ");
                    sink.word("or", false)?;
                    sink.ws(" ");
                    prose(sink, right, false, 4)?;
                }
                (CoreRef::Not, [inner]) => {
                    sink.word("not", initial)?;
                    sink.ws(" ");
                    prose(sink, inner, false, 5)?;
                }
                (CoreRef::Iff, [left, right]) => {
                    prose(sink, left, initial, 2)?;
                    sink.ws(" ");
                    sink.word("if", false)?;
                    sink.ws(" ");
                    sink.word("and", false)?;
                    sink.ws(" ");
                    sink.word("only", false)?;
                    sink.ws(" ");
                    sink.word("if", false)?;
                    sink.ws(" ");
                    prose(sink, right, false, 2)?;
                }
                _ => island(sink, term, false)?,
            },
            _ => island(sink, term, false)?,
        },
        _ => island(sink, term, false)?,
    }
    Ok(())
}

/// The text article for an existential binder (`a` or `an`), from the
/// binder type's canonical text form features (§13.5).
fn binder_article(closure: &Closure, binder: &Binder) -> &'static str {
    if let Term::Global(global, _) = &binder.ty {
        if let Some((_, entry)) = entry_for_global(closure, global) {
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
    match &binder.ty {
        Term::Global(global, _) => {
            let closure = sink.ctx.closure;
            match entry_for_global(closure, global).and_then(|(qualified, entry)| {
                entry
                    .forms
                    .iter()
                    .find(|form| form.canonical_source && form.channel.covers(Channel::Text))
                    .map(|form| (qualified, form.id.clone()))
            }) {
                Some((qualified, form_id)) => {
                    sink.form_surface(&qualified.package, &qualified.entry, &form_id)?;
                }
                None => island(sink, &binder.ty, false)?,
            }
        }
        other => island(sink, other, false)?,
    }
    sink.ws(" ");
    sink.structural("\\(", "math-open", "control");
    sink.local(binder.id);
    sink.structural("\\)", "math-close", "control");
    Ok(())
}

fn period(sink: &mut Sink<'_, '_>) {
    sink.structural(".", "period", "punctuation");
}

/// Canonical proof prose (§19.5).
#[allow(clippy::too_many_lines)]
fn proof_prose(sink: &mut Sink<'_, '_>, proof: &Proof) -> Result<(), Diagnostic> {
    match proof {
        Proof::Sequence(steps) => {
            for step in steps {
                proof_prose(sink, step)?;
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
                sink.local(*local);
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
                for premise in premises {
                    proof_prose(sink, premise)?;
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
            island(sink, proposition, false)?;
            period(sink);
            sink.ws("\n");
            proof_prose(sink, proof)?;
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
            for branch in branches {
                proof_prose(sink, branch)?;
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
            for case in cases {
                proof_prose(sink, &case.proof)?;
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
            for case in cases {
                proof_prose(sink, &case.proof)?;
            }
        }
        Proof::Calculate { start, steps, .. } => {
            // A displayed aligned chain (§19.5).
            sink.structural("\\[", "display-open", "control");
            math_term(sink, start, 0)?;
            for step in steps {
                sink.ws(" ");
                sink.tok("equals")?;
                sink.ws(" ");
                math_term(sink, &step.term, 51)?;
            }
            sink.structural("\\]", "display-close", "control");
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
            sink.local(*id);
            sink.structural("\\)", "math-close", "control");
        }
    }
    Ok(())
}

fn phrase_prose(sink: &mut Sink<'_, '_>, phrase: &Phrase) -> Result<(), Diagnostic> {
    for (index, item) in phrase.items.iter().enumerate() {
        if index > 0 {
            sink.ws(" ");
        }
        match item {
            PhraseItem::Word { entry, form } => {
                sink.form_surface(&entry.package, &entry.entry, form)?;
            }
            PhraseItem::Math(term) => island(sink, term, false)?,
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
    let ctx = Ctx { closure, spellings };
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
                        // Deterministic bold heading beyond two levels
                        // (§19.3), registered through the mathrm token.
                        sink.tok("mathrm")?;
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
                        sink.local(binder.id);
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
    let origin = checked
        .decl_origins
        .get(&declaration.component)
        .cloned()
        .unwrap_or(DeclOrigin {
            whole: (0, 0),
            sentence: (0, 0),
            proof: None,
        });
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
                prose(&mut sink, statement, true, 0)?;
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
        proof_prose(&mut sink, proof)?;
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
            sink.form_surface(
                &entry.package,
                &entry.entry,
                &canonical_text_form(glossary_entry)?,
            )?;
            sink.ws(" ");
            for word in ["is", "defined", "as"] {
                sink.word(word, false)?;
                sink.ws(" ");
            }
            island(sink, &rhs, false)?;
            period(sink);
        }
        DeclKind::TermDefinition => {
            self_head_prose(sink, entry, glossary_entry, &binders)?;
            sink.ws(" ");
            for word in ["is", "defined", "as"] {
                sink.word(word, false)?;
                sink.ws(" ");
            }
            island(sink, &rhs, false)?;
            period(sink);
        }
        DeclKind::PredicateDefinition => {
            self_head_prose(sink, entry, glossary_entry, &binders)?;
            sink.ws(" ");
            for word in ["holds", "exactly", "when"] {
                sink.word(word, false)?;
                sink.ws(" ");
            }
            prose(sink, &rhs, false, 0)?;
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

fn canonical_text_form(entry: &Entry) -> Result<String, Diagnostic> {
    entry
        .forms
        .iter()
        .find(|form| form.canonical_source && form.channel.covers(Channel::Text))
        .map(|form| form.id.clone())
        .ok_or_else(|| Diagnostic::new(code!("LLB6002"), "the entry has no canonical text form"))
}

fn self_head_prose(
    sink: &mut Sink<'_, '_>,
    entry_id: &QualifiedId,
    entry: &Entry,
    binders: &[Binder],
) -> Result<(), Diagnostic> {
    if binders.is_empty() {
        if let Ok(form) = canonical_text_form(entry) {
            return sink.form_surface(&entry_id.package, &entry_id.entry, &form);
        }
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
