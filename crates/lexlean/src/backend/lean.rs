//! The Lean backend (SPEC.md §18): prose-free, byte-deterministic Lean with
//! the exact §18.1 file structure, explicit fully qualified names, fixed
//! two-space tactic indentation, and lowering only to the pinned forms of
//! §18.7.

use std::collections::{BTreeMap, BTreeSet};

use crate::artifact::source_map::MapRole;
use crate::backend::{EmitSource, Emitter};
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::ir::declaration::{DeclBody, Declaration};
use crate::ir::document::DocumentModule;
use crate::ir::proof::{Proof, RewriteTarget};
use crate::ir::term::{Binder, CoreRef, GlobalRef, LocalId, Term, Universe};
use crate::lexicon::entry::Denotation;
use crate::lexicon::lse::{BinderMode, Lse, QualifiedId};
use crate::lexicon::resolve::Closure;
use crate::link::{CheckedModule, DeclOrigin};
use crate::source::coverage::Origin;

/// Deterministic generated names (§17.8): `llv#` for binders introduced by
/// terms and declarations, `llh#` for proof-introduced locals.
#[derive(Debug, Default)]
struct Namer {
    names: BTreeMap<LocalId, String>,
    term_count: usize,
    proof_count: usize,
}

impl Namer {
    fn term_binder(&mut self, id: LocalId) -> String {
        if let Some(existing) = self.names.get(&id) {
            return existing.clone();
        }
        let name = format!("llv{}", self.term_count);
        self.term_count += 1;
        self.names.insert(id, name.clone());
        name
    }

    fn proof_binder(&mut self, id: LocalId) -> String {
        if let Some(existing) = self.names.get(&id) {
            return existing.clone();
        }
        let name = format!("llh{}", self.proof_count);
        self.proof_count += 1;
        self.names.insert(id, name.clone());
        name
    }

    fn get(&mut self, id: LocalId) -> String {
        self.names
            .get(&id)
            .cloned()
            .unwrap_or_else(|| self.term_binder(id))
    }
}

/// A token sink bound to one origin context.
struct Sink<'a> {
    emitter: &'a mut Emitter,
    source: EmitSource,
    role: MapRole,
    node: usize,
}

impl Sink<'_> {
    fn kw(&mut self, text: &str) {
        self.emitter.piece(
            text,
            "keyword",
            Origin::Synthetic("core:lean-syntax/1".to_owned()),
            self.source.clone(),
            self.role,
            self.node,
        );
    }

    fn sym(&mut self, text: &str) {
        self.emitter.piece(
            text,
            "symbol",
            Origin::Synthetic("core:lean-syntax/1".to_owned()),
            self.source.clone(),
            self.role,
            self.node,
        );
    }

    fn ident(&mut self, text: &str, origin: Origin) {
        self.emitter.piece(
            text,
            "identifier",
            origin,
            self.source.clone(),
            self.role,
            self.node,
        );
    }

    fn numeral(&mut self, text: &str) {
        self.emitter.piece(
            text,
            "numeral",
            Origin::Numeral,
            self.source.clone(),
            self.role,
            self.node,
        );
    }

    fn ws(&mut self, text: &str) {
        self.emitter.ws(text);
    }
}

fn core_origin(core: CoreRef) -> Origin {
    let entry = match core {
        CoreRef::Eq => "eq",
        CoreRef::And => "land",
        CoreRef::Or => "lor",
        CoreRef::Not => "lnot",
        CoreRef::Iff => "iff",
        CoreRef::Exists | CoreRef::ExistsUnique => "exists",
    };
    Origin::Structural {
        package: "lexlean.core".to_owned(),
        entry: entry.to_owned(),
    }
}

fn global_lean_name(global: &GlobalRef, closure: &Closure) -> Result<String, Diagnostic> {
    match global {
        GlobalRef::Core(core) => Ok(core.lean_name().to_owned()),
        GlobalRef::External(external) => Ok(external.lean_name.clone()),
        GlobalRef::Document(document) => Ok(document.lean_name.clone()),
        GlobalRef::DefinedLexicon(defined) => {
            let qualified = QualifiedId::parse(&defined.entry).map_err(|reason| {
                Diagnostic::new(code!("LLI9001"), format!("phase lean-backend: {reason}"))
            })?;
            let entry = closure.entry(&qualified).ok_or_else(|| {
                Diagnostic::new(
                    code!("LLB6001"),
                    format!("`{qualified}` has no available defined value"),
                )
            })?;
            let Denotation::Defined { value, .. } = &entry.denotation else {
                return Err(Diagnostic::new(
                    code!("LLI9001"),
                    "phase lean-backend: defined reference to a non-defined entry",
                ));
            };
            print_defined_value(value, closure)
        }
    }
}

fn global_origin(global: &GlobalRef) -> Origin {
    match global {
        GlobalRef::Core(core) => core_origin(*core),
        GlobalRef::External(external) => {
            let (package, entry) = external
                .entry
                .split_once("::")
                .unwrap_or((external.package.as_str(), external.entry.as_str()));
            Origin::Form {
                package: package.to_owned(),
                entry: entry.to_owned(),
                form: "denotation".to_owned(),
            }
        }
        GlobalRef::Document(document) => Origin::Reference {
            module: document.module.clone(),
            component: document.component.clone(),
        },
        GlobalRef::DefinedLexicon(defined) => {
            let (package, entry) = defined
                .entry
                .split_once("::")
                .unwrap_or((defined.package.as_str(), defined.entry.as_str()));
            Origin::Form {
                package: package.to_owned(),
                entry: entry.to_owned(),
                form: "denotation".to_owned(),
            }
        }
    }
}

/// Print a defined lexicon value as one parenthesized Lean term with
/// canonical alpha-renamed binders (`x0`, `x1`, ...).
fn print_defined_value(value: &Lse, closure: &Closure) -> Result<String, Diagnostic> {
    fn walk(
        value: &Lse,
        closure: &Closure,
        scope: &mut Vec<(String, String)>,
        counter: &mut usize,
        parens: bool,
    ) -> Result<String, Diagnostic> {
        let out = match value {
            Lse::SortProp => "Prop".to_owned(),
            Lse::SortType(universe) => match universe {
                crate::lexicon::lse::Universe::Num(0) => "Type".to_owned(),
                crate::lexicon::lse::Universe::Num(n) => format!("Type {n}"),
                _ => {
                    return Err(Diagnostic::new(
                        code!("LLB6001"),
                        "a defined value with universe variables has no defined lowering",
                    ))
                }
            },
            Lse::Const(id, _) => {
                let entry = closure.entry(id).ok_or_else(|| {
                    Diagnostic::new(code!("LLB6001"), format!("`{id}` is unavailable"))
                })?;
                match &entry.denotation {
                    Denotation::Core { constructor } => {
                        crate::ir::term::CoreRef::from_constructor(constructor)
                            .map(|core| core.lean_name().to_owned())
                            .ok_or_else(|| {
                                Diagnostic::new(
                                    code!("LLB6001"),
                                    format!("core constructor `{constructor}` has no lowering"),
                                )
                            })?
                    }
                    Denotation::Lean { name, .. } => name.clone(),
                    Denotation::Defined { value: inner, .. } => {
                        walk(inner, closure, &mut Vec::new(), &mut 0, true)?
                    }
                    Denotation::Document { .. } => {
                        return Err(Diagnostic::new(
                            code!("LLB6001"),
                            "a defined value referencing a document declaration has no lowering here",
                        ));
                    }
                }
            }
            Lse::Local(name) => scope
                .iter()
                .rev()
                .find(|(original, _)| original == name)
                .map(|(_, renamed)| renamed.clone())
                .ok_or_else(|| {
                    Diagnostic::new(
                        code!("LLI9001"),
                        "phase lean-backend: unbound defined local",
                    )
                })?,
            Lse::App(function, arguments) => {
                let mut text = walk(function, closure, scope, counter, true)?;
                for argument in arguments {
                    text.push(' ');
                    text.push_str(&walk(argument, closure, scope, counter, true)?);
                }
                if parens {
                    format!("({text})")
                } else {
                    text
                }
            }
            Lse::Lam(binders, body) => {
                let depth = scope.len();
                let mut names = Vec::new();
                for binder in binders {
                    let fresh = format!("x{counter}");
                    *counter += 1;
                    scope.push((binder.name.clone(), fresh.clone()));
                    names.push(fresh);
                }
                let body_text = walk(body, closure, scope, counter, false)?;
                scope.truncate(depth);
                format!("(fun {} => {body_text})", names.join(" "))
            }
            Lse::Pi(..) | Lse::Let { .. } | Lse::Nat(_) => {
                return Err(Diagnostic::new(
                    code!("LLB6001"),
                    "this defined value form has no inline lowering",
                ));
            }
        };
        Ok(out)
    }
    walk(value, closure, &mut Vec::new(), &mut 0, true)
}

fn is_atomic(term: &Term) -> bool {
    matches!(
        term,
        Term::Local(_) | Term::Global(..) | Term::Sort(_) | Term::NatLiteral { .. }
    )
}

#[allow(clippy::too_many_lines)]
fn print_term(
    sink: &mut Sink<'_>,
    term: &Term,
    namer: &mut Namer,
    closure: &Closure,
    parens: bool,
) -> Result<(), Diagnostic> {
    match term {
        Term::Local(id) => {
            let name = namer.get(*id);
            sink.ident(&name, Origin::Local(id.0 as usize));
        }
        Term::Global(global, _) => {
            let name = global_lean_name(global, closure)?;
            sink.ident(&name, global_origin(global));
        }
        Term::Sort(universe) => match universe {
            Universe::Num(0) => sink.kw("Prop"),
            Universe::Num(1) => sink.kw("Type"),
            Universe::Num(n) => {
                sink.kw("Type");
                sink.ws(" ");
                sink.numeral(&(n - 1).to_string());
            }
            _ => {
                return Err(Diagnostic::new(
                    code!("LLB6001"),
                    "a universe variable has no defined lowering in a document term",
                ))
            }
        },
        Term::NatLiteral { decimal, .. } => sink.numeral(decimal),
        Term::App {
            function,
            explicit_args,
            ..
        } => {
            if parens {
                sink.sym("(");
            }
            print_term(sink, function, namer, closure, !is_atomic(function))?;
            for argument in explicit_args {
                sink.ws(" ");
                print_term(sink, argument, namer, closure, !is_atomic(argument))?;
            }
            if parens {
                sink.sym(")");
            }
        }
        Term::Pi { binders, body } => {
            if parens {
                sink.sym("(");
            }
            for binder in binders {
                if binder.spelling.is_empty() && !body_uses(body, binder.id) {
                    print_term(sink, &binder.ty, namer, closure, !is_atomic(&binder.ty))?;
                    sink.ws(" ");
                    sink.sym("→");
                    sink.ws(" ");
                } else {
                    let name = namer.term_binder(binder.id);
                    match binder.mode {
                        BinderMode::Explicit => sink.sym("("),
                        BinderMode::Implicit => sink.sym("{"),
                        BinderMode::Instance => sink.sym("["),
                    }
                    sink.ident(&name, Origin::Local(binder.id.0 as usize));
                    sink.ws(" ");
                    sink.sym(":");
                    sink.ws(" ");
                    print_term(sink, &binder.ty, namer, closure, false)?;
                    match binder.mode {
                        BinderMode::Explicit => sink.sym(")"),
                        BinderMode::Implicit => sink.sym("}"),
                        BinderMode::Instance => sink.sym("]"),
                    }
                    sink.ws(" ");
                    sink.sym("→");
                    sink.ws(" ");
                }
            }
            print_term(sink, body, namer, closure, false)?;
            if parens {
                sink.sym(")");
            }
        }
        Term::Lambda { binders, body } => {
            if parens {
                sink.sym("(");
            }
            sink.kw("fun");
            for binder in binders {
                let name = namer.term_binder(binder.id);
                sink.ws(" ");
                sink.ident(&name, Origin::Local(binder.id.0 as usize));
            }
            sink.ws(" ");
            sink.sym("=>");
            sink.ws(" ");
            print_term(sink, body, namer, closure, false)?;
            if parens {
                sink.sym(")");
            }
        }
        Term::Let {
            binder,
            value,
            body,
        } => {
            if parens {
                sink.sym("(");
            }
            sink.kw("let");
            sink.ws(" ");
            let name = namer.term_binder(binder.id);
            sink.ident(&name, Origin::Local(binder.id.0 as usize));
            sink.ws(" ");
            sink.sym(":");
            sink.ws(" ");
            print_term(sink, &binder.ty, namer, closure, false)?;
            sink.ws(" ");
            sink.sym(":=");
            sink.ws(" ");
            print_term(sink, value, namer, closure, false)?;
            sink.sym(";");
            sink.ws(" ");
            print_term(sink, body, namer, closure, false)?;
            if parens {
                sink.sym(")");
            }
        }
    }
    Ok(())
}

fn body_uses(term: &Term, id: LocalId) -> bool {
    let mut used = BTreeSet::new();
    collect_locals(term, &mut used);
    used.contains(&id)
}

fn collect_locals(term: &Term, out: &mut BTreeSet<LocalId>) {
    match term {
        Term::Local(id) => {
            out.insert(*id);
        }
        Term::Sort(_) | Term::Global(..) => {}
        Term::App {
            function,
            explicit_args,
            ..
        } => {
            collect_locals(function, out);
            for argument in explicit_args {
                collect_locals(argument, out);
            }
        }
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            for binder in binders {
                collect_locals(&binder.ty, out);
            }
            collect_locals(body, out);
        }
        Term::Let {
            binder,
            value,
            body,
        } => {
            collect_locals(&binder.ty, out);
            collect_locals(value, out);
            collect_locals(body, out);
        }
        Term::NatLiteral { expected_type, .. } => collect_locals(expected_type, out),
    }
}

#[allow(clippy::too_many_lines)]
fn print_proof(
    sink: &mut Sink<'_>,
    proof: &Proof,
    namer: &mut Namer,
    closure: &Closure,
    indent: usize,
) -> Result<(), Diagnostic> {
    let pad = "  ".repeat(indent);
    match proof {
        Proof::Sequence(steps) => {
            for step in steps {
                print_proof(sink, step, namer, closure, indent)?;
            }
        }
        Proof::Intro(locals) => {
            sink.ws(&pad);
            sink.kw("intro");
            for local in locals {
                let name = if namer.names.contains_key(local) {
                    namer.get(*local)
                } else {
                    namer.proof_binder(*local)
                };
                sink.ws(" ");
                sink.ident(&name, Origin::Local(local.0 as usize));
            }
            sink.ws("\n");
        }
        Proof::Exact(term) => {
            sink.ws(&pad);
            sink.kw("exact");
            sink.ws(" ");
            print_term(sink, term, namer, closure, false)?;
            sink.ws("\n");
        }
        Proof::ApplyOne(term) => {
            sink.ws(&pad);
            sink.kw("apply");
            sink.ws(" ");
            print_term(sink, term, namer, closure, false)?;
            sink.ws("\n");
        }
        Proof::Apply { function, premises } => {
            sink.ws(&pad);
            sink.kw("apply");
            sink.ws(" ");
            print_term(sink, function, namer, closure, false)?;
            sink.ws("\n");
            // Each premise proof closes its goal, so the sequences follow
            // in premise order on consecutive goals (§16.6).
            for premise in premises {
                print_proof(sink, premise, namer, closure, indent)?;
            }
        }
        Proof::Reflexivity => {
            sink.ws(&pad);
            sink.kw("rfl");
            sink.ws("\n");
        }
        Proof::Witness(term) => {
            sink.ws(&pad);
            sink.kw("refine");
            sink.ws(" ");
            sink.sym("⟨");
            print_term(sink, term, namer, closure, false)?;
            sink.sym(",");
            sink.ws(" ");
            sink.sym("?_");
            sink.sym("⟩");
            sink.ws("\n");
        }
        Proof::SelectLeft => {
            sink.ws(&pad);
            sink.kw("left");
            sink.ws("\n");
        }
        Proof::SelectRight => {
            sink.ws(&pad);
            sink.kw("right");
            sink.ws("\n");
        }
        Proof::Have {
            local,
            proposition,
            proof,
        } => {
            sink.ws(&pad);
            sink.kw("have");
            sink.ws(" ");
            let name = namer.proof_binder(*local);
            sink.ident(&name, Origin::Local(local.0 as usize));
            sink.ws(" ");
            sink.sym(":");
            sink.ws(" ");
            print_term(sink, proposition, namer, closure, false)?;
            sink.ws(" ");
            sink.sym(":=");
            sink.ws(" ");
            sink.kw("by");
            sink.ws("\n");
            print_proof(sink, proof, namer, closure, indent + 1)?;
        }
        Proof::Rewrite { target, rules } => {
            sink.ws(&pad);
            sink.kw("rw");
            sink.ws(" ");
            sink.sym("[");
            for (index, rule) in rules.iter().enumerate() {
                if index > 0 {
                    sink.sym(",");
                    sink.ws(" ");
                }
                if rule.reverse {
                    sink.sym("←");
                    sink.ws(" ");
                }
                print_term(sink, &rule.term, namer, closure, false)?;
            }
            sink.sym("]");
            if let RewriteTarget::Hypothesis(id) = target {
                sink.ws(" ");
                sink.kw("at");
                sink.ws(" ");
                let name = namer.get(*id);
                sink.ident(&name, Origin::Local(id.0 as usize));
            }
            sink.ws("\n");
        }
        Proof::SimplifyOnly { target, rules } => {
            sink.ws(&pad);
            sink.kw("simp");
            sink.ws(" ");
            sink.kw("only");
            sink.ws(" ");
            sink.sym("[");
            for (index, rule) in rules.iter().enumerate() {
                if index > 0 {
                    sink.sym(",");
                    sink.ws(" ");
                }
                print_term(sink, rule, namer, closure, false)?;
            }
            sink.sym("]");
            if let RewriteTarget::Hypothesis(id) = target {
                sink.ws(" ");
                sink.kw("at");
                sink.ws(" ");
                let name = namer.get(*id);
                sink.ident(&name, Origin::Local(id.0 as usize));
            }
            sink.ws("\n");
        }
        Proof::Constructor(branches) => {
            sink.ws(&pad);
            sink.kw("constructor");
            sink.ws("\n");
            for branch in branches {
                print_proof(sink, branch, namer, closure, indent)?;
            }
        }
        Proof::Cases { scrutinee, cases } | Proof::Induction { scrutinee, cases } => {
            sink.ws(&pad);
            sink.kw(if matches!(proof, Proof::Cases { .. }) {
                "cases"
            } else {
                "induction"
            });
            sink.ws(" ");
            print_term(sink, scrutinee, namer, closure, !is_atomic(scrutinee))?;
            sink.ws(" ");
            sink.kw("with");
            sink.ws("\n");
            for case in cases {
                sink.ws(&"  ".repeat(indent + 1));
                sink.sym("|");
                sink.ws(" ");
                let alternative = case
                    .lean_name
                    .rsplit('.')
                    .next()
                    .unwrap_or(case.lean_name.as_str());
                sink.ident(
                    alternative,
                    Origin::Form {
                        package: case.constructor.package.clone(),
                        entry: case.constructor.entry.clone(),
                        form: "denotation".to_owned(),
                    },
                );
                for (id, _) in &case.binders {
                    let name = namer.proof_binder(*id);
                    sink.ws(" ");
                    sink.ident(&name, Origin::Local(id.0 as usize));
                }
                sink.ws(" ");
                sink.sym("=>");
                sink.ws("\n");
                print_proof(sink, &case.proof, namer, closure, indent + 2)?;
            }
        }
        Proof::Calculate {
            relation,
            start,
            steps,
        } => {
            if !matches!(relation, GlobalRef::Core(CoreRef::Eq)) {
                return Err(Diagnostic::new(
                    code!("LLB6001"),
                    "language 1.0 lowers exactly the equality calculation descriptor",
                ));
            }
            sink.ws(&pad);
            sink.kw("calc");
            sink.ws(" ");
            print_term(sink, start, namer, closure, !is_atomic(start))?;
            let mut first = true;
            for step in steps {
                if first {
                    first = false;
                } else {
                    sink.ws("\n");
                    sink.ws(&"  ".repeat(indent + 1));
                    sink.sym("_");
                }
                sink.ws(" ");
                sink.sym("=");
                sink.ws(" ");
                print_term(sink, &step.term, namer, closure, !is_atomic(&step.term))?;
                sink.ws(" ");
                sink.sym(":=");
                sink.ws(" ");
                print_term(sink, &step.proof, namer, closure, !is_atomic(&step.proof))?;
            }
            sink.ws("\n");
        }
    }
    Ok(())
}

/// The sorted, deduplicated import list of one module (§18.3): external
/// entry modules plus the full generated names of document imports.
#[must_use]
pub fn module_imports(document: &DocumentModule, module_prefix: &str) -> Vec<String> {
    let mut imports: BTreeSet<String> = BTreeSet::new();
    let mut externals: BTreeMap<String, crate::ir::term::ExternalConstRef> = BTreeMap::new();
    crate::link::collect_document_externals(document, &mut externals);
    for external in externals.values() {
        imports.insert(external.lean_module.clone());
    }
    for import in &document.imports {
        imports.insert(format!("{module_prefix}.{import}"));
    }
    imports.into_iter().collect()
}

/// Render one module's canonical `.lean` (§18.1) through a tracing emitter.
#[allow(clippy::too_many_lines)]
pub fn render_module(
    checked: &CheckedModule,
    closure: &Closure,
    module_prefix: &str,
) -> Result<Emitter, Diagnostic> {
    let document = &checked.document;
    let mut emitter = Emitter::new();
    let preamble_node = emitter.node("lean-preamble");
    {
        let mut sink = Sink {
            emitter: &mut emitter,
            source: EmitSource::Synthetic("core:lean-preamble/1".to_owned()),
            role: MapRole::Synthetic,
            node: preamble_node,
        };
        sink.kw("module");
        sink.ws("\n");
        for import in module_imports(document, module_prefix) {
            sink.kw("import");
            sink.ws(" ");
            sink.ident(
                &import,
                Origin::Synthetic("core:lean-preamble/1".to_owned()),
            );
            sink.ws("\n");
        }
        sink.kw("set_option");
        sink.ws(" ");
        sink.ident(
            "autoImplicit",
            Origin::Synthetic("core:lean-preamble/1".to_owned()),
        );
        sink.ws(" ");
        sink.kw("false");
        sink.ws("\n");
        sink.kw("namespace");
        sink.ws(" ");
        sink.ident(
            &document.lean_module,
            Origin::Synthetic("core:lean-preamble/1".to_owned()),
        );
        sink.ws("\n");
    }

    for declaration in document.declarations() {
        emitter.ws("\n");
        let origin = checked
            .decl_origins
            .get(&declaration.component)
            .cloned()
            .unwrap_or(DeclOrigin {
                whole: (0, 0),
                sentence: (0, 0),
                proof: None,
            });
        render_declaration(&mut emitter, declaration, &origin, document, closure)?;
    }

    emitter.ws("\n");
    let end_node = emitter.node("lean-preamble");
    {
        let mut sink = Sink {
            emitter: &mut emitter,
            source: EmitSource::Synthetic("core:lean-preamble/1".to_owned()),
            role: MapRole::Synthetic,
            node: end_node,
        };
        sink.kw("end");
        sink.ws(" ");
        sink.ident(
            &document.lean_module,
            Origin::Synthetic("core:lean-preamble/1".to_owned()),
        );
        sink.ws("\n");
    }
    Ok(emitter)
}

fn render_declaration(
    emitter: &mut Emitter,
    declaration: &Declaration,
    origin: &DeclOrigin,
    document: &DocumentModule,
    closure: &Closure,
) -> Result<(), Diagnostic> {
    let node = emitter.node("declaration");
    let mut namer = Namer::default();
    match &declaration.body {
        DeclBody::TheoremLike { statement, proof } => {
            let mut sink = Sink {
                emitter,
                source: EmitSource::File(origin.whole.0, origin.whole.1),
                role: MapRole::Declaration,
                node,
            };
            // Lean 4.32.1's module system keeps declarations private to
            // their module unless marked `public`; the audit module and
            // cross-module imports require visibility (§18.9, §15.1).
            sink.kw("public");
            sink.ws(" ");
            sink.kw("theorem");
            sink.ws(" ");
            sink.ident(
                &declaration.lean_name,
                Origin::Reference {
                    module: document.name.clone(),
                    component: declaration.component.clone(),
                },
            );
            // Inherited section parameters, then lifted leading universal
            // binders (§18.3, §18.5), in scope order.
            sink.source = EmitSource::File(origin.sentence.0, origin.sentence.1);
            sink.role = MapRole::Term;
            for binder in &declaration.params {
                sink.ws(" ");
                print_param(&mut sink, binder, &mut namer, closure)?;
            }
            let mut rest = statement.clone();
            loop {
                match rest {
                    Term::Pi { ref binders, .. }
                        if binders.iter().all(|binder| !binder.spelling.is_empty()) =>
                    {
                        let Term::Pi { binders, body } = rest else {
                            unreachable!("matched above");
                        };
                        for binder in &binders {
                            sink.ws(" ");
                            print_param(&mut sink, binder, &mut namer, closure)?;
                        }
                        rest = *body;
                    }
                    _ => break,
                }
            }
            sink.ws(" ");
            sink.sym(":");
            sink.ws(" ");
            print_term(&mut sink, &rest, &mut namer, closure, false)?;
            sink.ws(" ");
            sink.sym(":=");
            sink.ws(" ");
            sink.kw("by");
            sink.ws("\n");
            if let Some(proof_range) = origin.proof {
                sink.source = EmitSource::File(proof_range.0, proof_range.1);
            }
            sink.role = MapRole::Proof;
            print_proof(&mut sink, proof, &mut namer, closure, 1)?;
        }
        DeclBody::Definition { ty, value, .. } => {
            let mut sink = Sink {
                emitter,
                source: EmitSource::File(origin.whole.0, origin.whole.1),
                role: MapRole::Declaration,
                node,
            };
            sink.kw("public");
            sink.ws(" ");
            sink.kw("def");
            sink.ws(" ");
            sink.ident(
                &declaration.lean_name,
                Origin::Reference {
                    module: document.name.clone(),
                    component: declaration.component.clone(),
                },
            );
            sink.source = EmitSource::File(origin.sentence.0, origin.sentence.1);
            sink.role = MapRole::Term;
            for binder in &declaration.params {
                sink.ws(" ");
                print_param(&mut sink, binder, &mut namer, closure)?;
            }
            // Lift lambda binders into declaration parameters when they
            // mirror the leading signature binders (§18.6).
            let (params, result_ty, body) = match (ty, value) {
                (
                    Term::Pi {
                        binders: type_binders,
                        body: type_body,
                    },
                    Term::Lambda { binders, body },
                ) if binders.len() == type_binders.len() => {
                    (binders.clone(), (**type_body).clone(), (**body).clone())
                }
                _ => (Vec::new(), ty.clone(), value.clone()),
            };
            // The value lambda binds its own locals; the printed result type
            // must reference them, so rename type binders to value binders.
            let result_ty = if params.is_empty() {
                result_ty
            } else if let Term::Pi {
                binders: type_binders,
                ..
            } = ty
            {
                let map: BTreeMap<LocalId, Term> = type_binders
                    .iter()
                    .zip(&params)
                    .map(|(from, to)| (from.id, Term::Local(to.id)))
                    .collect();
                crate::elaborate::expressions::subst(&result_ty, &map)
            } else {
                result_ty
            };
            for binder in &params {
                sink.ws(" ");
                print_param(&mut sink, binder, &mut namer, closure)?;
            }
            sink.ws(" ");
            sink.sym(":");
            sink.ws(" ");
            print_term(&mut sink, &result_ty, &mut namer, closure, false)?;
            sink.ws(" ");
            sink.sym(":=");
            sink.ws("\n");
            sink.ws("  ");
            print_term(&mut sink, &body, &mut namer, closure, false)?;
            sink.ws("\n");
        }
    }
    Ok(())
}

fn print_param(
    sink: &mut Sink<'_>,
    binder: &Binder,
    namer: &mut Namer,
    closure: &Closure,
) -> Result<(), Diagnostic> {
    let name = namer.term_binder(binder.id);
    match binder.mode {
        BinderMode::Explicit => sink.sym("("),
        BinderMode::Implicit => sink.sym("{"),
        BinderMode::Instance => sink.sym("["),
    }
    sink.ident(&name, Origin::Local(binder.id.0 as usize));
    sink.ws(" ");
    sink.sym(":");
    sink.ws(" ");
    print_term(sink, &binder.ty, namer, closure, false)?;
    match binder.mode {
        BinderMode::Explicit => sink.sym(")"),
        BinderMode::Implicit => sink.sym("}"),
        BinderMode::Instance => sink.sym("]"),
    }
    Ok(())
}

/// Print an LSE signature as a Lean type expression, for the probe module
/// (§18.8). Universe variables are alpha-renamed with the entry-index
/// prefix.
pub fn print_lse_type(
    lse: &Lse,
    closure: &Closure,
    universe_prefix: &str,
) -> Result<String, Diagnostic> {
    fn universe_text(universe: &crate::lexicon::lse::Universe, prefix: &str) -> String {
        match universe {
            crate::lexicon::lse::Universe::Num(n) => n.to_string(),
            crate::lexicon::lse::Universe::Var(name) => format!("{prefix}{name}"),
            crate::lexicon::lse::Universe::Succ(inner) => {
                format!("({} + 1)", universe_text(inner, prefix))
            }
            crate::lexicon::lse::Universe::Max(items) => {
                let mut text = "(max".to_owned();
                for item in items {
                    text.push(' ');
                    text.push_str(&universe_text(item, prefix));
                }
                text.push(')');
                text
            }
            crate::lexicon::lse::Universe::IMax(a, b) => format!(
                "(imax {} {})",
                universe_text(a, prefix),
                universe_text(b, prefix)
            ),
        }
    }
    fn walk(
        lse: &Lse,
        closure: &Closure,
        prefix: &str,
        scope: &mut Vec<String>,
        parens: bool,
    ) -> Result<String, Diagnostic> {
        let out = match lse {
            Lse::SortProp => "Prop".to_owned(),
            Lse::SortType(universe) => match universe {
                crate::lexicon::lse::Universe::Num(0) => "Type".to_owned(),
                crate::lexicon::lse::Universe::Num(n) => format!("Type {n}"),
                other => format!("Type {}", universe_text(other, prefix)),
            },
            Lse::Const(id, _) => {
                let entry = closure.entry(id).ok_or_else(|| {
                    Diagnostic::new(code!("LLB6001"), format!("`{id}` is unavailable"))
                })?;
                match &entry.denotation {
                    Denotation::Core { constructor } => CoreRef::from_constructor(constructor)
                        .map(|core| core.lean_name().to_owned())
                        .ok_or_else(|| {
                            Diagnostic::new(
                                code!("LLB6001"),
                                format!("core constructor `{constructor}` has no lowering"),
                            )
                        })?,
                    Denotation::Lean { name, .. } => name.clone(),
                    Denotation::Defined { value, .. } => print_defined_value(value, closure)?,
                    Denotation::Document { .. } => {
                        return Err(Diagnostic::new(
                            code!("LLB6001"),
                            "a probe signature referencing a document declaration has no lowering",
                        ));
                    }
                }
            }
            Lse::Local(name) => name.clone(),
            Lse::App(function, arguments) => {
                let mut text = walk(function, closure, prefix, scope, true)?;
                for argument in arguments {
                    text.push(' ');
                    text.push_str(&walk(argument, closure, prefix, scope, true)?);
                }
                if parens {
                    format!("({text})")
                } else {
                    text
                }
            }
            Lse::Pi(binders, body) => {
                let mut text = String::new();
                for binder in binders {
                    let (open, close) = match binder.mode {
                        BinderMode::Explicit => ('(', ')'),
                        BinderMode::Implicit => ('{', '}'),
                        BinderMode::Instance => ('[', ']'),
                    };
                    text.push(open);
                    text.push_str(&binder.name);
                    text.push_str(" : ");
                    text.push_str(&walk(&binder.ty, closure, prefix, scope, false)?);
                    text.push(close);
                    text.push_str(" → ");
                    scope.push(binder.name.clone());
                }
                text.push_str(&walk(body, closure, prefix, scope, false)?);
                for _ in binders {
                    scope.pop();
                }
                if parens {
                    format!("({text})")
                } else {
                    text
                }
            }
            Lse::Lam(..) | Lse::Let { .. } | Lse::Nat(_) => {
                return Err(Diagnostic::new(
                    code!("LLB6001"),
                    "this LSE form has no probe-type lowering",
                ));
            }
        };
        Ok(out)
    }
    walk(lse, closure, universe_prefix, &mut Vec::new(), false)
}

/// The probe module source (§18.8).
pub fn probe_module(
    semantic_hex32: &str,
    externals: &BTreeMap<String, crate::ir::term::ExternalConstRef>,
    closure: &Closure,
) -> Result<(String, String), Diagnostic> {
    let name = format!("LexLeanProbe.P{semantic_hex32}");
    let mut imports: BTreeSet<String> = BTreeSet::new();
    for external in externals.values() {
        imports.insert(external.lean_module.clone());
    }
    let mut text = String::from("module\n");
    for import in &imports {
        text.push_str(&format!("import {import}\n"));
    }
    text.push_str("set_option autoImplicit false\n");
    for (index, (entry_id, external)) in externals.iter().enumerate() {
        let qualified = QualifiedId::parse(entry_id).map_err(|reason| {
            Diagnostic::new(code!("LLI9001"), format!("phase probe: {reason}"))
        })?;
        let entry = closure.entry(&qualified).ok_or_else(|| {
            Diagnostic::new(code!("LLB6001"), format!("`{qualified}` is unavailable"))
        })?;
        let signature = entry.signature.as_ref().ok_or_else(|| {
            Diagnostic::new(code!("LLB6001"), format!("`{qualified}` has no signature"))
        })?;
        let prefix = format!("p{index}");
        let universes = if entry.universes.is_empty() {
            String::new()
        } else {
            let list: Vec<String> = entry
                .universes
                .iter()
                .map(|name| format!("{prefix}{name}"))
                .collect();
            format!(".{{{}}}", list.join(", "))
        };
        let ty = print_lse_type(signature, closure, &prefix)?;
        text.push_str(&format!(
            "example{universes} : {ty} := {}\n",
            external.lean_name
        ));
    }
    Ok((name, text))
}

/// The axiom-audit module source (§18.9): imports every generated module in
/// sorted order and prints axioms for every declaration in sorted fully
/// qualified name order.
#[must_use]
pub fn audit_module(
    semantic_hex32: &str,
    generated_modules: &[String],
    declaration_names: &[String],
) -> (String, String) {
    let name = format!("LexLeanAudit.A{semantic_hex32}");
    let mut text = String::from("module\n");
    let mut sorted_modules = generated_modules.to_vec();
    sorted_modules.sort();
    for module in &sorted_modules {
        text.push_str(&format!("import {module}\n"));
    }
    let mut sorted_names = declaration_names.to_vec();
    sorted_names.sort();
    for declaration in &sorted_names {
        text.push_str(&format!("#print axioms {declaration}\n"));
    }
    (name, text)
}
