//! The Lean backend (SPEC.md §18): prose-free, byte-deterministic Lean with
//! the exact §18.1 file structure, explicit fully qualified names, fixed
//! two-space tactic indentation, and lowering only to the pinned forms of
//! §18.7.
//!
//! Disclosed lowering decisions that the pinned toolchain forces:
//!
//! - **Unique existence.** Lean 4.32.1's `Init` has no `ExistsUnique`
//!   constant, so the core `ExistsUnique (fun (x : T) => P)` term lowers to
//!   its definitional expansion
//!   `Exists (fun (x : T) => And (P) ((y : T) → P[x:=y] → Eq y x))`, with
//!   deterministic binder names and every application parenthesized. The
//!   IR keeps `ExistsUnique`; only the printed bytes change. A `Witness`
//!   step therefore leaves the `And` goal for the remaining proof.
//! - **Numerals** (§18.4) print bare only as an explicit argument of an
//!   application whose applied signature fixes the parameter type to a
//!   monomorphic constant (`Nat.add llv0 0`); everywhere else they carry
//!   the elaborated expected type as `(0 : Nat)`.
//! - **Section parameters** are printed explicitly on each declaration that
//!   uses them, in scope order and closed under type dependencies (§18.3),
//!   as ordinary explicit binders `(llvN : T)` before the lifted leading
//!   universal binders (§18.5).

use std::collections::{BTreeMap, BTreeSet};

use crate::artifact::source_map::MapRole;
use crate::backend::{EmitSource, Emitter};
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::ir::declaration::{DeclBody, Declaration};
use crate::ir::document::{Block, DocumentModule};
use crate::ir::proof::{Proof, RewriteTarget};
use crate::ir::term::{
    Binder, CoreRef, DefinedLexiconRef, ExternalConstRef, GlobalRef, LocalId, Term, Universe,
};
use crate::lexicon::entry::{Denotation, Entry};
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
    synthetic_count: u64,
    /// The locals this declaration's generated Lean references (§17.8; see
    /// [`declaration_uses`]). A binder outside this set is bound and never
    /// mentioned, so its generated name carries the `_` prefix that marks a
    /// deliberate binding: pinned Lean's `unusedVariables` linter warns
    /// otherwise, and a warning fails verification (§20.2).
    used: BTreeSet<LocalId>,
}

impl Namer {
    fn for_declaration(declaration: &Declaration, ctx: TermCtx<'_>) -> Self {
        let mut used = BTreeSet::new();
        // The analysis reads the declaration exactly as it will be printed,
        // so it needs the same synthetic identities the printer allocates;
        // this scratch namer supplies them and is then discarded.
        let mut scratch = Self::default();
        // An inherited section parameter may be named only by a later
        // parameter's type (`(llv0 : Nat) (llv1 : Fin llv0)`, §18.3), which
        // the statement no longer holds: the parameter types are part of
        // what the declaration references.
        for param in &declaration.params {
            collect_uses(&param.ty, ctx, &mut scratch, &mut used);
        }
        declaration_uses(&declaration.body, ctx, &mut scratch, &mut used);
        Self {
            used,
            ..Self::default()
        }
    }

    /// The name of a binder at `index` in its class: the §17.8 spelling,
    /// prefixed by `_` when nothing references it.
    fn binder_name(&self, prefix: &str, index: usize, id: LocalId) -> String {
        if self.used.contains(&id) {
            format!("{prefix}{index}")
        } else {
            format!("_{prefix}{index}")
        }
    }

    fn term_binder(&mut self, id: LocalId) -> String {
        if let Some(existing) = self.names.get(&id) {
            return existing.clone();
        }
        let name = self.binder_name("llv", self.term_count, id);
        self.term_count += 1;
        self.names.insert(id, name.clone());
        name
    }

    fn proof_binder(&mut self, id: LocalId) -> String {
        if let Some(existing) = self.names.get(&id) {
            return existing.clone();
        }
        let name = self.binder_name("llh", self.proof_count, id);
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

    /// A compiler-invented binder identity that no elaborated local can
    /// share (elaboration allocates upward from zero). The backend names a
    /// synthetic binder only where it also references it, so the identity
    /// counts as used.
    fn synthetic(&mut self) -> LocalId {
        self.synthetic_count += 1;
        let id = LocalId(u64::MAX - self.synthetic_count);
        self.used.insert(id);
        id
    }
}

/// Every document definition of the linked project by `(module,
/// component)`, so a declaration rendered in one module can read a type
/// definition declared in another (§17.7: an import exposes all exported
/// declarations of the imported module).
pub struct DocumentAliases<'a> {
    values: BTreeMap<(&'a str, &'a str), &'a Term>,
}

impl<'a> DocumentAliases<'a> {
    /// Collect the definitions of every module the build renders.
    pub fn of_documents(documents: impl IntoIterator<Item = &'a DocumentModule>) -> Self {
        let mut values = BTreeMap::new();
        for document in documents {
            for declaration in document.declarations() {
                if let DeclBody::Definition { value, .. } = &declaration.body {
                    values.insert(
                        (document.name.as_str(), declaration.component.as_str()),
                        value,
                    );
                }
            }
        }
        Self { values }
    }

    /// The type a numeral's expected type is ascribed at: a document type
    /// definition is replaced by what it is defined as, in any module of
    /// the project (README, documented deviations: a numeral is ascribed
    /// `(0 : Nat)`, never `(0 : count)`). Lean's `OfNat` instances live on
    /// the underlying type and a generated `def count : Type := Nat` is
    /// not unfolded during instance synthesis, so an alias ascription
    /// cannot elaborate --- in the defining module exactly as in an
    /// importing one. Each step consumes one distinct declaration, whose
    /// identity bounds the walk; document definitions are acyclic (§15.7
    /// rule 8) and the `seen` set makes that independent of the check.
    fn ascription(&self, expected: &'a Term) -> &'a Term {
        let mut current = expected;
        let mut seen: BTreeSet<(&str, &str)> = BTreeSet::new();
        while let Term::Global(GlobalRef::Document(reference), _) = current {
            let key = (reference.module.as_str(), reference.component.as_str());
            if !seen.insert(key) {
                return current;
            }
            let Some(value) = self.values.get(&key) else {
                return current;
            };
            current = value;
        }
        current
    }
}

/// A token sink bound to one origin context.
struct Sink<'a> {
    emitter: &'a mut Emitter,
    source: EmitSource,
    role: MapRole,
    node: usize,
    /// The project's document definitions, for numeral ascription.
    aliases: &'a DocumentAliases<'a>,
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

    /// A symbol whose origin is not Lean syntax the backend chose but the
    /// glossary value it was inlined from (`emit_global`).
    fn emit_symbol(&mut self, text: &str, origin: Origin) {
        self.emitter.piece(
            text,
            "symbol",
            origin,
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

fn internal(message: impl std::fmt::Display) -> Diagnostic {
    Diagnostic::new(code!("LLI9001"), format!("phase lean-backend: {message}"))
}

fn qualified_of(text: &str) -> Result<QualifiedId, Diagnostic> {
    QualifiedId::parse(text).map_err(internal)
}

fn global_lean_name(global: &GlobalRef, closure: &Closure) -> Result<String, Diagnostic> {
    match global {
        GlobalRef::Core(core) => Ok(core.lean_name().to_owned()),
        GlobalRef::External(external) => Ok(external.lean_name.clone()),
        GlobalRef::Document(document) => Ok(document.lean_name.clone()),
        GlobalRef::DefinedLexicon(defined) => {
            let qualified = qualified_of(&defined.entry)?;
            let entry = closure.entry(&qualified).ok_or_else(|| {
                Diagnostic::new(
                    code!("LLB6001"),
                    format!("`{qualified}` has no available defined value"),
                )
            })?;
            let Denotation::Defined { value, .. } = &entry.denotation else {
                return Err(internal("defined reference to a non-defined entry"));
            };
            print_defined_value(value, closure)
        }
    }
}

/// Emit one global's generated Lean.
///
/// Every global but a defined lexicon value prints as one identifier. A
/// defined value (§13.6) is *inlined*: its Lean text is a complete term,
/// often a lambda or an application, and emitting it as a single
/// identifier token would give the whole inlined term one coverage row and
/// one source mapping (§20.3, §20.5) — the granularity of the smallest
/// enclosing mapping a Lean diagnostic can be remapped to (§20.4) would
/// then be the entire inlined value. It is therefore emitted token by
/// token. The split is lexical and total, so the concatenated bytes are
/// exactly the printed value; every token carries the glossary form the
/// value denotes, because that is where each of them comes from.
fn emit_global(sink: &mut Sink<'_>, global: &GlobalRef, text: &str) {
    let origin = global_origin(global);
    if !matches!(global, GlobalRef::DefinedLexicon(_)) {
        sink.ident(text, origin);
        return;
    }
    let is_ident = |c: char| c.is_alphanumeric() || c == '_' || c == '.' || c == '\'' || c == '!';
    let mut rest = text;
    while !rest.is_empty() {
        let width = |predicate: fn(char) -> bool| {
            rest.chars()
                .take_while(|c| predicate(*c))
                .map(char::len_utf8)
                .sum::<usize>()
        };
        let (piece, kind) = if rest.starts_with(char::is_whitespace) {
            (&rest[..width(char::is_whitespace)], TokenKind::Space)
        } else if rest.starts_with(|c: char| c.is_ascii_digit()) {
            (&rest[..width(|c| c.is_ascii_digit())], TokenKind::Numeral)
        } else if rest.starts_with(is_ident) {
            (&rest[..width(is_ident)], TokenKind::Identifier)
        } else {
            let width = rest.chars().next().map_or(0, char::len_utf8);
            (&rest[..width], TokenKind::Symbol)
        };
        match kind {
            TokenKind::Space => sink.ws(piece),
            TokenKind::Numeral => sink.numeral(piece),
            TokenKind::Identifier => sink.ident(piece, origin.clone()),
            TokenKind::Symbol => sink.emit_symbol(piece, origin.clone()),
        }
        rest = &rest[piece.len()..];
    }
}

/// The lexical classes an inlined defined value splits into.
#[derive(Clone, Copy)]
enum TokenKind {
    Space,
    Numeral,
    Identifier,
    Symbol,
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

// ---------------------------------------------------------------------------
// LSE printing (defined values and probe signatures)
// ---------------------------------------------------------------------------

/// The one printer for LSE values as Lean terms: locals are alpha-renamed
/// to `x0`, `x1`, ... in binding order, applications and binders are fully
/// parenthesized, and universe variables carry an optional prefix (§18.8).
struct LsePrinter<'c> {
    closure: &'c Closure,
    /// The universe-variable prefix; `None` rejects universe variables
    /// (an inlined defined value has no universe context of its own).
    universe_prefix: Option<&'c str>,
    /// Bound locals: original name, printed name, declared type.
    scope: Vec<(String, String, Lse)>,
    counter: usize,
}

fn universe_text(universe: &crate::lexicon::lse::Universe, prefix: &str) -> String {
    use crate::lexicon::lse::Universe as U;
    match universe {
        U::Num(n) => n.to_string(),
        U::Var(name) => format!("{prefix}{name}"),
        U::Succ(inner) => format!("({} + 1)", universe_text(inner, prefix)),
        U::Max(items) => {
            let mut text = "(max".to_owned();
            for item in items {
                text.push(' ');
                text.push_str(&universe_text(item, prefix));
            }
            text.push(')');
            text
        }
        U::IMax(a, b) => format!(
            "(imax {} {})",
            universe_text(a, prefix),
            universe_text(b, prefix)
        ),
    }
}

/// Collect the alpha-renamed universe variable names of one LSE value.
fn collect_universe_vars(lse: &Lse, prefix: &str, out: &mut Vec<String>) {
    fn universe_vars(
        universe: &crate::lexicon::lse::Universe,
        prefix: &str,
        out: &mut Vec<String>,
    ) {
        use crate::lexicon::lse::Universe as U;
        match universe {
            U::Num(_) => {}
            U::Var(name) => {
                let renamed = format!("{prefix}{name}");
                if !out.contains(&renamed) {
                    out.push(renamed);
                }
            }
            U::Succ(inner) => universe_vars(inner, prefix, out),
            U::Max(items) => items
                .iter()
                .for_each(|item| universe_vars(item, prefix, out)),
            U::IMax(a, b) => {
                universe_vars(a, prefix, out);
                universe_vars(b, prefix, out);
            }
        }
    }
    match lse {
        Lse::SortProp | Lse::Local(_) | Lse::Nat(_) => {}
        Lse::SortType(universe) => universe_vars(universe, prefix, out),
        Lse::Const(_, universes) => universes
            .iter()
            .for_each(|universe| universe_vars(universe, prefix, out)),
        Lse::App(function, arguments) => {
            collect_universe_vars(function, prefix, out);
            arguments
                .iter()
                .for_each(|argument| collect_universe_vars(argument, prefix, out));
        }
        Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
            binders
                .iter()
                .for_each(|binder| collect_universe_vars(&binder.ty, prefix, out));
            collect_universe_vars(body, prefix, out);
        }
        Lse::Let {
            ty, value, body, ..
        } => {
            collect_universe_vars(ty, prefix, out);
            collect_universe_vars(value, prefix, out);
            collect_universe_vars(body, prefix, out);
        }
    }
}

/// Substitute LSE locals by name (capture is impossible: the substituted
/// values are closed argument terms of the same application).
fn lse_subst(lse: &Lse, map: &BTreeMap<String, Lse>) -> Lse {
    match lse {
        Lse::Local(name) => map.get(name).cloned().unwrap_or_else(|| lse.clone()),
        Lse::SortProp | Lse::SortType(_) | Lse::Const(..) | Lse::Nat(_) => lse.clone(),
        Lse::App(function, arguments) => Lse::App(
            Box::new(lse_subst(function, map)),
            arguments
                .iter()
                .map(|argument| lse_subst(argument, map))
                .collect(),
        ),
        Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
            let mut inner = map.clone();
            let binders: Vec<crate::lexicon::lse::LseBinder> = binders
                .iter()
                .map(|binder| {
                    let renamed = crate::lexicon::lse::LseBinder {
                        name: binder.name.clone(),
                        mode: binder.mode,
                        ty: lse_subst(&binder.ty, &inner),
                    };
                    inner.remove(&binder.name);
                    renamed
                })
                .collect();
            let body = Box::new(lse_subst(body, &inner));
            if matches!(lse, Lse::Pi(..)) {
                Lse::Pi(binders, body)
            } else {
                Lse::Lam(binders, body)
            }
        }
        Lse::Let {
            name,
            ty,
            value,
            body,
        } => {
            let mut inner = map.clone();
            inner.remove(name);
            Lse::Let {
                name: name.clone(),
                ty: Box::new(lse_subst(ty, map)),
                value: Box::new(lse_subst(value, map)),
                body: Box::new(lse_subst(body, &inner)),
            }
        }
    }
}

/// Is an LSE type closed enough to serve as a numeral ascription: no free
/// locals remain after argument substitution?
fn lse_is_closed(lse: &Lse, bound: &[String]) -> bool {
    match lse {
        Lse::Local(name) => bound.contains(name),
        Lse::SortProp | Lse::SortType(_) | Lse::Const(..) | Lse::Nat(_) => true,
        Lse::App(function, arguments) => {
            lse_is_closed(function, bound)
                && arguments
                    .iter()
                    .all(|argument| lse_is_closed(argument, bound))
        }
        Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
            let mut inner = bound.to_vec();
            for binder in binders {
                if !lse_is_closed(&binder.ty, &inner) {
                    return false;
                }
                inner.push(binder.name.clone());
            }
            lse_is_closed(body, &inner)
        }
        Lse::Let {
            name,
            ty,
            value,
            body,
        } => {
            let mut inner = bound.to_vec();
            inner.push(name.clone());
            lse_is_closed(ty, bound) && lse_is_closed(value, bound) && lse_is_closed(body, &inner)
        }
    }
}

impl LsePrinter<'_> {
    fn binder_delims(mode: BinderMode) -> (char, char) {
        match mode {
            BinderMode::Explicit => ('(', ')'),
            BinderMode::Implicit => ('{', '}'),
            BinderMode::Instance => ('[', ']'),
        }
    }

    fn bind(&mut self, name: &str, ty: &Lse) -> String {
        let fresh = format!("x{}", self.counter);
        self.counter += 1;
        self.scope
            .push((name.to_owned(), fresh.clone(), ty.clone()));
        fresh
    }

    fn constant(&self, id: &QualifiedId) -> Result<String, Diagnostic> {
        let entry = self
            .closure
            .entry(id)
            .ok_or_else(|| Diagnostic::new(code!("LLB6001"), format!("`{id}` is unavailable")))?;
        match &entry.denotation {
            Denotation::Core { constructor } => CoreRef::from_constructor(constructor)
                .map(|core| core.lean_name().to_owned())
                .ok_or_else(|| {
                    Diagnostic::new(
                        code!("LLB6001"),
                        format!("core constructor `{constructor}` has no lowering"),
                    )
                }),
            Denotation::Lean { name, .. } => Ok(name.clone()),
            Denotation::Defined { value, .. } => print_defined_value(value, self.closure),
            Denotation::Document { .. } => Err(Diagnostic::new(
                code!("LLB6001"),
                format!(
                    "`{id}` denotes a document declaration and has no lowering outside its module"
                ),
            )),
        }
    }

    /// The declared parameter types of an applied LSE constant, for numeral
    /// ascription: binder `i` after substituting the preceding arguments.
    fn parameter_types(&self, function: &Lse, arguments: &[Lse]) -> Vec<Option<Lse>> {
        let mut out = vec![None; arguments.len()];
        let Lse::Const(id, _) = function else {
            return out;
        };
        let Some(entry) = self.closure.entry(id) else {
            return out;
        };
        let Some(Lse::Pi(binders, _)) = &entry.signature else {
            return out;
        };
        // LSE applications supply explicit arguments only (§13.8, §17.6):
        // implicit and instance binders are inferred by Lean, so the
        // argument at position `index` instantiates the `index`-th explicit
        // binder; earlier non-explicit binders stay unsubstituted (their
        // types are then not closed and yield no ascription).
        let mut map: BTreeMap<String, Lse> = BTreeMap::new();
        let mut index = 0usize;
        for binder in binders {
            if !matches!(binder.mode, BinderMode::Explicit) {
                continue;
            }
            let Some(argument) = arguments.get(index) else {
                break;
            };
            let ty = lse_subst(&binder.ty, &map);
            let bound: Vec<String> = self.scope.iter().map(|(name, ..)| name.clone()).collect();
            if lse_is_closed(&ty, &bound) {
                out[index] = Some(ty);
            }
            map.insert(binder.name.clone(), argument.clone());
            index += 1;
        }
        out
    }

    fn universe(&self, universe: &crate::lexicon::lse::Universe) -> Result<String, Diagnostic> {
        match self.universe_prefix {
            Some(prefix) => Ok(universe_text(universe, prefix)),
            None => {
                let mut vars = Vec::new();
                collect_universe_vars(&Lse::SortType(universe.clone()), "", &mut vars);
                if vars.is_empty() {
                    Ok(universe_text(universe, ""))
                } else {
                    Err(Diagnostic::new(
                        code!("LLB6001"),
                        "a defined value with universe variables has no inline lowering",
                    ))
                }
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn walk(
        &mut self,
        lse: &Lse,
        parens: bool,
        expected: Option<&Lse>,
    ) -> Result<String, Diagnostic> {
        let out = match lse {
            Lse::SortProp => "Prop".to_owned(),
            Lse::SortType(universe) => match universe {
                crate::lexicon::lse::Universe::Num(0) => "Type".to_owned(),
                crate::lexicon::lse::Universe::Num(n) => format!("Type {n}"),
                other => format!("Type {}", self.universe(other)?),
            },
            Lse::Const(id, universes) => {
                let mut text = self.constant(id)?;
                if !universes.is_empty() {
                    let list: Vec<String> = universes
                        .iter()
                        .map(|universe| self.universe(universe))
                        .collect::<Result<_, _>>()?;
                    text = format!("{text}.{{{}}}", list.join(", "));
                }
                text
            }
            Lse::Local(name) => self
                .scope
                .iter()
                .rev()
                .find(|(original, ..)| original == name)
                .map(|(_, renamed, _)| renamed.clone())
                .ok_or_else(|| internal(format!("unbound LSE local `{name}`")))?,
            Lse::App(function, arguments) => {
                let parameter_types = self.parameter_types(function, arguments);
                // LSE applications supply explicit arguments only; Lean
                // infers the implicit and instance binders (§17.6).
                let mut text = self.walk(function, true, None)?;
                for (index, argument) in arguments.iter().enumerate() {
                    text.push(' ');
                    let expected = parameter_types.get(index).and_then(Option::as_ref);
                    text.push_str(&self.walk(argument, true, expected)?);
                }
                if parens {
                    format!("({text})")
                } else {
                    text
                }
            }
            Lse::Pi(binders, body) => {
                let depth = self.scope.len();
                let mut text = String::new();
                for binder in binders {
                    let (open, close) = Self::binder_delims(binder.mode);
                    let ty = self.walk(&binder.ty, false, None)?;
                    let name = self.bind(&binder.name, &binder.ty);
                    text.push(open);
                    text.push_str(&name);
                    text.push_str(" : ");
                    text.push_str(&ty);
                    text.push(close);
                    text.push_str(" → ");
                }
                text.push_str(&self.walk(body, false, None)?);
                self.scope.truncate(depth);
                if parens {
                    format!("({text})")
                } else {
                    text
                }
            }
            Lse::Lam(binders, body) => {
                let depth = self.scope.len();
                let mut text = String::from("fun");
                for binder in binders {
                    let (open, close) = Self::binder_delims(binder.mode);
                    let ty = self.walk(&binder.ty, false, None)?;
                    let name = self.bind(&binder.name, &binder.ty);
                    text.push(' ');
                    text.push(open);
                    text.push_str(&name);
                    text.push_str(" : ");
                    text.push_str(&ty);
                    text.push(close);
                }
                text.push_str(" => ");
                text.push_str(&self.walk(body, false, None)?);
                self.scope.truncate(depth);
                format!("({text})")
            }
            Lse::Let {
                name,
                ty,
                value,
                body,
            } => {
                let depth = self.scope.len();
                let ty_text = self.walk(ty, false, None)?;
                let value_text = self.walk(value, false, Some(ty))?;
                let fresh = self.bind(name, ty);
                let body_text = self.walk(body, false, None)?;
                self.scope.truncate(depth);
                format!("(let {fresh} : {ty_text} := {value_text}; {body_text})")
            }
            Lse::Nat(decimal) => match expected {
                Some(ty) => {
                    let ty_text = self.walk(ty, false, None)?;
                    format!("({decimal} : {ty_text})")
                }
                None => decimal.clone(),
            },
        };
        Ok(out)
    }
}

/// Print a defined lexicon value as one parenthesized Lean term with
/// canonical alpha-renamed binders (`x0`, `x1`, ...). Nested defined values
/// inline recursively; numerals carry the applied signature's parameter
/// type when it is closed.
fn print_defined_value(value: &Lse, closure: &Closure) -> Result<String, Diagnostic> {
    let mut printer = LsePrinter {
        closure,
        universe_prefix: None,
        scope: Vec::new(),
        counter: 0,
    };
    printer.walk(value, true, None)
}

/// Print an LSE signature as a Lean type expression, for the probe module
/// (§18.8). Universe variables are alpha-renamed with the entry-index
/// prefix; locals are alpha-renamed to `x0`, `x1`, ...; numerals carry the
/// applied signature's parameter type when the enclosing binder type is
/// known and closed.
pub fn print_lse_type(
    lse: &Lse,
    closure: &Closure,
    universe_prefix: &str,
) -> Result<String, Diagnostic> {
    let mut printer = LsePrinter {
        closure,
        universe_prefix: Some(universe_prefix),
        scope: Vec::new(),
        counter: 0,
    };
    printer.walk(lse, false, None)
}

// ---------------------------------------------------------------------------
// Term printing
// ---------------------------------------------------------------------------

/// The beta-reduct of a saturated application of a defined lexicon value
/// (§13.6): the value's body with each binder replaced by the applied
/// argument term. Generated Lean then states the definition's meaning
/// directly, exactly as the elaborator read it (§17.6 unfolds the same
/// value), instead of applying a lambda in place. `None` — the application
/// prints as the applied lambda, which is the same term — when the body
/// holds an LSE form with no backend term equivalent: a numeral, whose
/// expected type only elaboration determines; a document denotation, whose
/// generated name is linked per module; a core constructor with no closed
/// global (the implication arrow is a `Pi`, not a constant); or an entry
/// without a signature hash.
fn beta_reduce_defined(
    global: &GlobalRef,
    args: &[Term],
    ctx: TermCtx<'_>,
    namer: &mut Namer,
) -> Option<Term> {
    let GlobalRef::DefinedLexicon(defined) = global else {
        return None;
    };
    let qualified = QualifiedId::parse(&defined.entry).ok()?;
    let entry = ctx.closure.entry(&qualified)?;
    let Denotation::Defined { value, .. } = &entry.denotation else {
        return None;
    };
    let Lse::Lam(binders, body) = value else {
        return None;
    };
    if binders.len() != args.len()
        || binders
            .iter()
            .any(|binder| binder.mode != BinderMode::Explicit)
    {
        return None;
    }
    let mut scope: Vec<(String, Term)> = Vec::new();
    for (binder, argument) in binders.iter().zip(args) {
        scope.push((binder.name.clone(), argument.clone()));
    }
    lse_body_term(body, ctx, namer, &mut scope)
}

/// Convert a defined value's body to a term, resolving constants through
/// the closure and locals through `scope` (see [`beta_reduce_defined`]).
fn lse_body_term(
    lse: &Lse,
    ctx: TermCtx<'_>,
    namer: &mut Namer,
    scope: &mut Vec<(String, Term)>,
) -> Option<Term> {
    Some(match lse {
        Lse::SortProp => Term::Sort(Universe::Num(0)),
        Lse::SortType(universe) => Term::Sort(Universe::Succ(Box::new(lse_universe(universe)))),
        Lse::Const(id, universes) => Term::Global(
            defined_body_global(id, ctx)?,
            universes.iter().map(lse_universe).collect(),
        ),
        Lse::Local(name) => scope
            .iter()
            .rev()
            .find(|(bound, _)| bound == name)
            .map(|(_, term)| term.clone())?,
        Lse::App(function, arguments) => {
            let function = lse_body_term(function, ctx, namer, scope)?;
            let mut explicit_args = Vec::with_capacity(arguments.len());
            for argument in arguments {
                explicit_args.push(lse_body_term(argument, ctx, namer, scope)?);
            }
            Term::App {
                function: Box::new(function),
                explicit_args,
                omitted_implicit_binders: Vec::new(),
            }
        }
        Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
            let depth = scope.len();
            let mut ir_binders = Vec::with_capacity(binders.len());
            for binder in binders {
                let Some(ty) = lse_body_term(&binder.ty, ctx, namer, scope) else {
                    scope.truncate(depth);
                    return None;
                };
                let id = namer.synthetic();
                scope.push((binder.name.clone(), Term::Local(id)));
                ir_binders.push(Binder {
                    id,
                    mode: binder.mode,
                    ty,
                    spelling: binder.name.clone(),
                });
            }
            let body = lse_body_term(body, ctx, namer, scope);
            scope.truncate(depth);
            let body = Box::new(body?);
            if matches!(lse, Lse::Pi(..)) {
                Term::Pi {
                    binders: ir_binders,
                    body,
                }
            } else {
                Term::Lambda {
                    binders: ir_binders,
                    body,
                }
            }
        }
        // A numeral needs the expected type elaboration determined, and a
        // `let` binder needs its value's type; neither is available here.
        Lse::Nat(_) | Lse::Let { .. } => return None,
    })
}

/// The global a constant in a defined value's body denotes.
fn defined_body_global(id: &QualifiedId, ctx: TermCtx<'_>) -> Option<GlobalRef> {
    let entry = ctx.closure.entry(id)?;
    Some(match &entry.denotation {
        Denotation::Core { constructor } => {
            GlobalRef::Core(CoreRef::from_constructor(constructor)?)
        }
        Denotation::Lean { module, name } => GlobalRef::External(ExternalConstRef {
            package: id.package.clone(),
            entry: id.to_string(),
            lean_module: module.clone(),
            lean_name: name.clone(),
            signature_hash: entry.signature_hash?,
        }),
        Denotation::Defined { .. } => GlobalRef::DefinedLexicon(DefinedLexiconRef {
            package: id.package.clone(),
            entry: id.to_string(),
            signature_hash: entry.signature_hash?,
        }),
        Denotation::Document { .. } => return None,
    })
}

/// An LSE universe as an IR universe.
fn lse_universe(universe: &crate::lexicon::lse::Universe) -> Universe {
    match universe {
        crate::lexicon::lse::Universe::Num(n) => Universe::Num(*n),
        crate::lexicon::lse::Universe::Var(name) => Universe::Var(name.clone()),
        crate::lexicon::lse::Universe::Succ(inner) => Universe::Succ(Box::new(lse_universe(inner))),
        crate::lexicon::lse::Universe::Max(items) => {
            Universe::Max(items.iter().map(lse_universe).collect())
        }
        crate::lexicon::lse::Universe::IMax(left, right) => {
            Universe::IMax(Box::new(lse_universe(left)), Box::new(lse_universe(right)))
        }
    }
}

fn is_atomic(term: &Term) -> bool {
    match term {
        Term::Local(_) | Term::Global(..) | Term::Sort(_) | Term::NatLiteral { .. } => true,
        // An application without explicit arguments prints as its head.
        Term::App {
            function,
            explicit_args,
            ..
        } => explicit_args.is_empty() && is_atomic(function),
        _ => false,
    }
}

/// Does a monomorphic constant parameter type admit a bare numeral in the
/// generated Lean? Only a constant Lean itself knows: Lean elaborates the
/// numeral against the parameter type it sees, and `OfNat` instances are
/// found for `Nat`, not for a name that merely unfolds to it. A document
/// declaration and a defined lexicon value are both printed as (or under)
/// an alias Lean has no instance for — `def count : Type := Nat` makes
/// `f 2` a `synthInstanceFailed` — so those positions ascribe the unfolded
/// type instead (§18.4).
fn const_admits_bare_numeral(ty: &Lse, closure: &Closure) -> bool {
    let Lse::Const(id, universes) = ty else {
        return false;
    };
    universes.is_empty()
        && matches!(
            closure.entry(id).map(|entry| &entry.denotation),
            Some(Denotation::Lean { .. })
        )
}

/// Which explicit arguments of an application may carry a bare numeral
/// (§18.4): those whose applied signature binder is a monomorphic constant
/// type Lean knows. Everything else ascribes.
fn bare_numeral_positions(function: &Term, closure: &Closure, arity: usize) -> Vec<bool> {
    let mut out = vec![false; arity];
    let Term::Global(global, _) = function else {
        return out;
    };
    let entry: &Entry = match global {
        GlobalRef::External(external) => match QualifiedId::parse(&external.entry)
            .ok()
            .and_then(|qualified| closure.entry(&qualified))
        {
            Some(entry) => entry,
            None => return out,
        },
        GlobalRef::DefinedLexicon(defined) => match QualifiedId::parse(&defined.entry)
            .ok()
            .and_then(|qualified| closure.entry(&qualified))
        {
            Some(entry) => entry,
            None => return out,
        },
        // A document declaration is declared by exactly one glossary entry
        // whose denotation names it (§13.6, §15.7); its signature fixes the
        // parameter types the same way an external signature does.
        GlobalRef::Document(document) => match closure.packages.iter().find_map(|package| {
            package.entries.values().find(|entry| {
                matches!(
                    &entry.denotation,
                    Denotation::Document { module, component }
                        if *module == document.module && *component == document.component
                )
            })
        }) {
            Some(entry) => entry,
            None => return out,
        },
        GlobalRef::Core(_) => return out,
    };
    let Some(Lse::Pi(binders, _)) = &entry.signature else {
        return out;
    };
    let explicit: Vec<&crate::lexicon::lse::LseBinder> = binders
        .iter()
        .filter(|binder| matches!(binder.mode, BinderMode::Explicit))
        .collect();
    for (index, slot) in out.iter_mut().enumerate() {
        if let Some(binder) = explicit.get(index) {
            *slot = const_admits_bare_numeral(&binder.ty, closure);
        }
    }
    out
}

/// What printing a document term needs beyond the term: the glossary
/// closure, and the module whose declarations a document reference may
/// have to be unfolded through (a numeral's expected type, §18.4).
#[derive(Clone, Copy)]
struct TermCtx<'a> {
    closure: &'a Closure,
}

fn print_binder_open(sink: &mut Sink<'_>, mode: BinderMode) {
    match mode {
        BinderMode::Explicit => sink.sym("("),
        BinderMode::Implicit => sink.sym("{"),
        BinderMode::Instance => sink.sym("["),
    }
}

fn print_binder_close(sink: &mut Sink<'_>, mode: BinderMode) {
    match mode {
        BinderMode::Explicit => sink.sym(")"),
        BinderMode::Implicit => sink.sym("}"),
        BinderMode::Instance => sink.sym("]"),
    }
}

/// The unique-existence expansion (module documentation): given the bound
/// binder and body of `ExistsUnique (fun x => P)`, print
/// `Exists (fun (x : T) => And (P) ((y : T) → P[x:=y] → Eq y x))`.
fn print_exists_unique(
    sink: &mut Sink<'_>,
    binder: &Binder,
    body: &Term,
    namer: &mut Namer,
    ctx: TermCtx<'_>,
    parens: bool,
) -> Result<(), Diagnostic> {
    if parens {
        sink.sym("(");
    }
    sink.ident("Exists", core_origin(CoreRef::Exists));
    sink.ws(" ");
    sink.sym("(");
    sink.kw("fun");
    sink.ws(" ");
    let x_name = namer.term_binder(binder.id);
    sink.sym("(");
    sink.ident(&x_name, Origin::Local(binder.id.0 as usize));
    sink.ws(" ");
    sink.sym(":");
    sink.ws(" ");
    print_term(sink, &binder.ty, namer, ctx, false, false)?;
    sink.sym(")");
    sink.ws(" ");
    sink.sym("=>");
    sink.ws(" ");
    sink.ident("And", core_origin(CoreRef::And));
    sink.ws(" ");
    sink.sym("(");
    print_term(sink, body, namer, ctx, false, false)?;
    sink.sym(")");
    sink.ws(" ");
    // The uniqueness binder is a renamed copy of the source binder; it
    // traces to the same local.
    let y_id = namer.synthetic();
    let y_name = namer.term_binder(y_id);
    let mut map = BTreeMap::new();
    map.insert(binder.id, Term::Local(y_id));
    let renamed = crate::elaborate::expressions::subst(body, &map);
    sink.sym("(");
    sink.sym("(");
    sink.ident(&y_name, Origin::Local(binder.id.0 as usize));
    sink.ws(" ");
    sink.sym(":");
    sink.ws(" ");
    print_term(sink, &binder.ty, namer, ctx, false, false)?;
    sink.sym(")");
    sink.ws(" ");
    sink.sym("→");
    sink.ws(" ");
    print_term(sink, &renamed, namer, ctx, !is_atomic(&renamed), false)?;
    sink.ws(" ");
    sink.sym("→");
    sink.ws(" ");
    sink.ident("Eq", core_origin(CoreRef::Eq));
    sink.ws(" ");
    sink.ident(&y_name, Origin::Local(binder.id.0 as usize));
    sink.ws(" ");
    sink.ident(&x_name, Origin::Local(binder.id.0 as usize));
    sink.sym(")");
    sink.sym(")");
    if parens {
        sink.sym(")");
    }
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn print_term(
    sink: &mut Sink<'_>,
    term: &Term,
    namer: &mut Namer,
    ctx: TermCtx<'_>,
    parens: bool,
    bare_numeral: bool,
) -> Result<(), Diagnostic> {
    match term {
        Term::Local(id) => {
            let name = namer.get(*id);
            sink.ident(&name, Origin::Local(id.0 as usize));
        }
        Term::Global(global, _) => {
            let name = global_lean_name(global, ctx.closure)?;
            emit_global(sink, global, &name);
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
        Term::NatLiteral {
            decimal,
            expected_type,
        } => {
            if bare_numeral {
                sink.numeral(decimal);
            } else {
                // Lean resolves the numeral's `OfNat` instance against the
                // ascribed type as written, so a document type alias must
                // be ascribed unfolded (§18.4): `(2 : Nat)`, never
                // `(2 : count)` for `def count : Type := Nat`, in whichever
                // module of the linked project defines the alias.
                let ascription = sink.aliases.ascription(expected_type);
                sink.sym("(");
                sink.numeral(decimal);
                sink.ws(" ");
                sink.sym(":");
                sink.ws(" ");
                print_term(sink, ascription, namer, ctx, false, false)?;
                sink.sym(")");
            }
        }
        Term::App {
            function,
            explicit_args,
            ..
        } => {
            if let (
                Term::Global(GlobalRef::Core(CoreRef::ExistsUnique), _),
                [Term::Lambda { binders, body }],
            ) = (&**function, explicit_args.as_slice())
            {
                if let [binder] = binders.as_slice() {
                    return print_exists_unique(sink, binder, body, namer, ctx, parens);
                }
            }
            // A saturated application of a defined lexicon value prints as
            // its beta-reduct (§13.6, §18.4): the value's meaning, not a
            // lambda applied in place.
            if let Term::Global(global, _) = &**function {
                if let Some(reduced) = beta_reduce_defined(global, explicit_args, ctx, namer) {
                    return print_term(sink, &reduced, namer, ctx, parens, false);
                }
            }
            // An application with no explicit arguments (an atom whose
            // implicit parameters Lean infers) prints as its head.
            if explicit_args.is_empty() {
                return print_term(sink, function, namer, ctx, parens, false);
            }
            if parens {
                sink.sym("(");
            }
            print_term(sink, function, namer, ctx, !is_atomic(function), false)?;
            let bare = bare_numeral_positions(function, ctx.closure, explicit_args.len());
            for (index, argument) in explicit_args.iter().enumerate() {
                sink.ws(" ");
                print_term(
                    sink,
                    argument,
                    namer,
                    ctx,
                    !is_atomic(argument),
                    bare.get(index).copied().unwrap_or(false),
                )?;
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
                    print_term(sink, &binder.ty, namer, ctx, !is_atomic(&binder.ty), false)?;
                    sink.ws(" ");
                    sink.sym("→");
                    sink.ws(" ");
                } else {
                    let name = namer.term_binder(binder.id);
                    print_binder_open(sink, binder.mode);
                    sink.ident(&name, Origin::Local(binder.id.0 as usize));
                    sink.ws(" ");
                    sink.sym(":");
                    sink.ws(" ");
                    print_term(sink, &binder.ty, namer, ctx, false, false)?;
                    print_binder_close(sink, binder.mode);
                    sink.ws(" ");
                    sink.sym("→");
                    sink.ws(" ");
                }
            }
            print_term(sink, body, namer, ctx, false, false)?;
            if parens {
                sink.sym(")");
            }
        }
        Term::Lambda { binders, body } => {
            if parens {
                sink.sym("(");
            }
            // Binders are typed so Lean never has to infer a lambda's
            // domain (`Exists (fun (x : Nat) => ...)`).
            sink.kw("fun");
            for binder in binders {
                let name = namer.term_binder(binder.id);
                sink.ws(" ");
                print_binder_open(sink, binder.mode);
                sink.ident(&name, Origin::Local(binder.id.0 as usize));
                sink.ws(" ");
                sink.sym(":");
                sink.ws(" ");
                print_term(sink, &binder.ty, namer, ctx, false, false)?;
                print_binder_close(sink, binder.mode);
            }
            sink.ws(" ");
            sink.sym("=>");
            sink.ws(" ");
            print_term(sink, body, namer, ctx, false, false)?;
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
            print_term(sink, &binder.ty, namer, ctx, false, false)?;
            sink.ws(" ");
            sink.sym(":=");
            sink.ws(" ");
            print_term(sink, value, namer, ctx, false, false)?;
            sink.sym(";");
            sink.ws(" ");
            print_term(sink, body, namer, ctx, false, false)?;
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

/// Every local a declaration's generated Lean references: the locals of
/// its statement, definition type and value, and every proof term, plus a
/// hypothesis a rewrite or simplification names as its target. A binder
/// introduction (a `Pi`/`Lambda`/`Let` binder, an `intro`, a `have`, a case
/// binder) is not a reference, so a binder whose identity is absent here is
/// bound and unused.
fn declaration_uses(
    body: &DeclBody,
    ctx: TermCtx<'_>,
    scratch: &mut Namer,
    out: &mut BTreeSet<LocalId>,
) {
    match body {
        DeclBody::TheoremLike { statement, proof } => {
            collect_uses(statement, ctx, scratch, out);
            proof_uses(proof, ctx, scratch, out);
        }
        DeclBody::Definition { ty, value, .. } => {
            collect_uses(ty, ctx, scratch, out);
            collect_uses(value, ctx, scratch, out);
        }
    }
}

/// The locals a term references *as printed*: a saturated application of a
/// defined lexicon value prints as its beta-reduct, and a reduct may drop
/// an argument (a value whose body ignores a binder), so the locals of the
/// dropped argument are not referenced by the generated Lean and their
/// binders must carry the `_` prefix (§17.8 deviation, README).
fn collect_uses(term: &Term, ctx: TermCtx<'_>, scratch: &mut Namer, out: &mut BTreeSet<LocalId>) {
    if let Term::App {
        function,
        explicit_args,
        ..
    } = term
    {
        if let Term::Global(global, _) = &**function {
            if let Some(reduced) = beta_reduce_defined(global, explicit_args, ctx, scratch) {
                collect_uses(&reduced, ctx, scratch, out);
                return;
            }
        }
    }
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
            collect_uses(function, ctx, scratch, out);
            for argument in explicit_args {
                collect_uses(argument, ctx, scratch, out);
            }
        }
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            for binder in binders {
                collect_uses(&binder.ty, ctx, scratch, out);
            }
            collect_uses(body, ctx, scratch, out);
        }
        Term::Let {
            binder,
            value,
            body,
        } => {
            collect_uses(&binder.ty, ctx, scratch, out);
            collect_uses(value, ctx, scratch, out);
            collect_uses(body, ctx, scratch, out);
        }
        Term::NatLiteral { expected_type, .. } => collect_uses(expected_type, ctx, scratch, out),
    }
}

/// The locals a proof references (see [`declaration_uses`]).
fn proof_uses(proof: &Proof, ctx: TermCtx<'_>, scratch: &mut Namer, out: &mut BTreeSet<LocalId>) {
    let target_use = |target: &RewriteTarget, out: &mut BTreeSet<LocalId>| {
        if let RewriteTarget::Hypothesis(id) = target {
            out.insert(*id);
        }
    };
    match proof {
        Proof::Sequence(steps) => {
            for step in steps {
                proof_uses(step, ctx, scratch, out);
            }
        }
        // `intro` binds; it does not reference.
        Proof::Intro(_) | Proof::Reflexivity | Proof::SelectLeft | Proof::SelectRight => {}
        Proof::Exact(term) | Proof::ApplyOne(term) | Proof::Witness(term) => {
            collect_uses(term, ctx, scratch, out);
        }
        Proof::Apply { function, premises } => {
            collect_uses(function, ctx, scratch, out);
            for premise in premises {
                proof_uses(premise, ctx, scratch, out);
            }
        }
        Proof::Have {
            proposition, proof, ..
        } => {
            collect_uses(proposition, ctx, scratch, out);
            proof_uses(proof, ctx, scratch, out);
        }
        Proof::Rewrite { target, rules } => {
            target_use(target, out);
            for rule in rules {
                collect_uses(&rule.term, ctx, scratch, out);
            }
        }
        Proof::SimplifyOnly { target, rules } => {
            target_use(target, out);
            for rule in rules {
                collect_uses(rule, ctx, scratch, out);
            }
        }
        Proof::Constructor(branches) => {
            for branch in branches {
                proof_uses(branch, ctx, scratch, out);
            }
        }
        Proof::Cases { scrutinee, cases } | Proof::Induction { scrutinee, cases } => {
            collect_uses(scrutinee, ctx, scratch, out);
            for case in cases {
                proof_uses(&case.proof, ctx, scratch, out);
            }
        }
        Proof::Calculate { start, steps, .. } => {
            collect_uses(start, ctx, scratch, out);
            for step in steps {
                collect_uses(&step.term, ctx, scratch, out);
                collect_uses(&step.proof, ctx, scratch, out);
            }
        }
    }
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

// ---------------------------------------------------------------------------
// Proof printing
// ---------------------------------------------------------------------------

/// The per-step source ranges of one proof in pre-order (§20.3), consumed
/// as the proof IR is walked.
struct StepCursor<'a> {
    steps: &'a [(usize, usize)],
    next: usize,
}

impl StepCursor<'_> {
    fn take(&mut self) -> Result<(usize, usize), Diagnostic> {
        let range = self
            .steps
            .get(self.next)
            .copied()
            .ok_or_else(|| internal("proof-step origin count does not match the proof IR"))?;
        self.next += 1;
        Ok(range)
    }
}

fn print_term_expr(
    sink: &mut Sink<'_>,
    term: &Term,
    namer: &mut Namer,
    ctx: TermCtx<'_>,
) -> Result<(), Diagnostic> {
    print_term(sink, term, namer, ctx, false, false)
}

#[allow(clippy::too_many_lines)]
fn print_proof(
    sink: &mut Sink<'_>,
    proof: &Proof,
    namer: &mut Namer,
    ctx: TermCtx<'_>,
    indent: usize,
    steps: &mut StepCursor<'_>,
) -> Result<(), Diagnostic> {
    let pad = "  ".repeat(indent);
    if !matches!(proof, Proof::Sequence(_)) {
        let (start, end) = steps.take()?;
        sink.source = EmitSource::File(start, end);
    }
    match proof {
        Proof::Sequence(inner) => {
            for step in inner {
                print_proof(sink, step, namer, ctx, indent, steps)?;
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
            print_term_expr(sink, term, namer, ctx)?;
            sink.ws("\n");
        }
        Proof::ApplyOne(term) => {
            sink.ws(&pad);
            sink.kw("apply");
            sink.ws(" ");
            print_term_expr(sink, term, namer, ctx)?;
            sink.ws("\n");
        }
        Proof::Apply { function, premises } => {
            sink.ws(&pad);
            sink.kw("apply");
            sink.ws(" ");
            print_term_expr(sink, function, namer, ctx)?;
            sink.ws("\n");
            // Each premise proof closes its goal, so the sequences follow
            // in premise order on consecutive goals (§16.6).
            for premise in premises {
                print_proof(sink, premise, namer, ctx, indent, steps)?;
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
            print_term_expr(sink, term, namer, ctx)?;
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
            print_term_expr(sink, proposition, namer, ctx)?;
            sink.ws(" ");
            sink.sym(":=");
            sink.ws(" ");
            sink.kw("by");
            sink.ws("\n");
            print_proof(sink, proof, namer, ctx, indent + 1, steps)?;
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
                print_term_expr(sink, &rule.term, namer, ctx)?;
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
                print_term_expr(sink, rule, namer, ctx)?;
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
                print_proof(sink, branch, namer, ctx, indent, steps)?;
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
            print_term(sink, scrutinee, namer, ctx, !is_atomic(scrutinee), false)?;
            sink.ws(" ");
            sink.kw("with");
            sink.ws("\n");
            let head_source = sink.source.clone();
            for case in cases {
                sink.source = head_source.clone();
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
                print_proof(sink, &case.proof, namer, ctx, indent + 2, steps)?;
            }
        }
        Proof::Calculate {
            relation,
            start,
            steps: chain,
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
            print_term(sink, start, namer, ctx, !is_atomic(start), false)?;
            let mut first = true;
            for step in chain {
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
                print_term(sink, &step.term, namer, ctx, !is_atomic(&step.term), false)?;
                sink.ws(" ");
                sink.sym(":=");
                sink.ws(" ");
                print_term(
                    sink,
                    &step.proof,
                    namer,
                    ctx,
                    !is_atomic(&step.proof),
                    false,
                )?;
            }
            sink.ws("\n");
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Externals: imports and the probe set
// ---------------------------------------------------------------------------

/// The external reference of a Lean-denoting entry. An entry without a
/// signature has no interface to probe and no hash to record, so it yields
/// no reference; the constructs that name it (a `cases` alternative) do so
/// only through the type whose own reference carries the import.
fn external_of(entry_id: &QualifiedId, entry: &Entry) -> Option<ExternalConstRef> {
    let Denotation::Lean { module, name } = &entry.denotation else {
        return None;
    };
    Some(ExternalConstRef {
        package: entry_id.package.clone(),
        entry: entry_id.to_string(),
        lean_module: module.clone(),
        lean_name: name.clone(),
        signature_hash: entry.signature_hash?,
    })
}

/// Every Lean constant an LSE value reaches (through nested defined values
/// too), keyed by qualified entry ID.
fn lse_externals(
    lse: &Lse,
    closure: &Closure,
    out: &mut BTreeMap<String, ExternalConstRef>,
    visiting: &mut BTreeSet<String>,
) {
    match lse {
        Lse::Const(id, _) => {
            let Some(entry) = closure.entry(id) else {
                return;
            };
            match &entry.denotation {
                Denotation::Lean { .. } => {
                    if let Some(external) = external_of(id, entry) {
                        out.insert(id.to_string(), external);
                    }
                }
                Denotation::Defined { value, .. } => {
                    // Defined values are acyclic (§13.11); the visiting set
                    // is defense in depth against a corrupt closure.
                    if visiting.insert(id.to_string()) {
                        lse_externals(value, closure, out, visiting);
                        visiting.remove(&id.to_string());
                    }
                }
                Denotation::Core { .. } | Denotation::Document { .. } => {}
            }
        }
        Lse::SortProp | Lse::SortType(_) | Lse::Local(_) | Lse::Nat(_) => {}
        Lse::App(function, arguments) => {
            lse_externals(function, closure, out, visiting);
            for argument in arguments {
                lse_externals(argument, closure, out, visiting);
            }
        }
        Lse::Pi(binders, body) | Lse::Lam(binders, body) => {
            for binder in binders {
                lse_externals(&binder.ty, closure, out, visiting);
            }
            lse_externals(body, closure, out, visiting);
        }
        Lse::Let {
            ty, value, body, ..
        } => {
            lse_externals(ty, closure, out, visiting);
            lse_externals(value, closure, out, visiting);
            lse_externals(body, closure, out, visiting);
        }
    }
}

fn term_indirect_externals(
    term: &Term,
    closure: &Closure,
    out: &mut BTreeMap<String, ExternalConstRef>,
) {
    match term {
        Term::Global(GlobalRef::DefinedLexicon(defined), _) => {
            if let Ok(qualified) = QualifiedId::parse(&defined.entry) {
                if let Some(entry) = closure.entry(&qualified) {
                    if let Denotation::Defined { value, .. } = &entry.denotation {
                        lse_externals(value, closure, out, &mut BTreeSet::new());
                    }
                }
            }
        }
        Term::Global(..) | Term::Local(_) | Term::Sort(_) => {}
        Term::App {
            function,
            explicit_args,
            ..
        } => {
            term_indirect_externals(function, closure, out);
            for argument in explicit_args {
                term_indirect_externals(argument, closure, out);
            }
        }
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            for binder in binders {
                term_indirect_externals(&binder.ty, closure, out);
            }
            term_indirect_externals(body, closure, out);
        }
        Term::Let {
            binder,
            value,
            body,
        } => {
            term_indirect_externals(&binder.ty, closure, out);
            term_indirect_externals(value, closure, out);
            term_indirect_externals(body, closure, out);
        }
        Term::NatLiteral { expected_type, .. } => {
            term_indirect_externals(expected_type, closure, out);
        }
    }
}

fn proof_indirect_externals(
    proof: &Proof,
    closure: &Closure,
    out: &mut BTreeMap<String, ExternalConstRef>,
) {
    match proof {
        Proof::Sequence(steps) => steps
            .iter()
            .for_each(|step| proof_indirect_externals(step, closure, out)),
        Proof::Exact(term) | Proof::ApplyOne(term) | Proof::Witness(term) => {
            term_indirect_externals(term, closure, out);
        }
        Proof::Apply { function, premises } => {
            term_indirect_externals(function, closure, out);
            premises
                .iter()
                .for_each(|premise| proof_indirect_externals(premise, closure, out));
        }
        Proof::Have {
            proposition, proof, ..
        } => {
            term_indirect_externals(proposition, closure, out);
            proof_indirect_externals(proof, closure, out);
        }
        Proof::Rewrite { rules, .. } => rules
            .iter()
            .for_each(|rule| term_indirect_externals(&rule.term, closure, out)),
        Proof::SimplifyOnly { rules, .. } => rules
            .iter()
            .for_each(|rule| term_indirect_externals(rule, closure, out)),
        Proof::Constructor(branches) => branches
            .iter()
            .for_each(|branch| proof_indirect_externals(branch, closure, out)),
        Proof::Cases { scrutinee, cases } | Proof::Induction { scrutinee, cases } => {
            term_indirect_externals(scrutinee, closure, out);
            for case in cases {
                // The case constructor is an external Lean constant even
                // though the tactic names only its last segment.
                if let Some(entry) = closure.entry(&case.constructor) {
                    if let Some(external) = external_of(&case.constructor, entry) {
                        out.insert(case.constructor.to_string(), external);
                    }
                }
                proof_indirect_externals(&case.proof, closure, out);
            }
        }
        Proof::Calculate { start, steps, .. } => {
            term_indirect_externals(start, closure, out);
            for step in steps {
                term_indirect_externals(&step.term, closure, out);
                term_indirect_externals(&step.proof, closure, out);
            }
        }
        Proof::Intro(_) | Proof::Reflexivity | Proof::SelectLeft | Proof::SelectRight => {}
    }
}

/// Every external Lean constant one document reaches (§18.3, §18.8): direct
/// external globals, Lean constants inside inlined defined lexicon values
/// (transitively), and the constructors named by `cases`/`induction`
/// branches. Keyed by qualified entry ID.
#[must_use]
pub fn document_externals(
    document: &DocumentModule,
    closure: &Closure,
) -> BTreeMap<String, ExternalConstRef> {
    fn walk_blocks(
        blocks: &[Block],
        closure: &Closure,
        out: &mut BTreeMap<String, ExternalConstRef>,
    ) {
        for block in blocks {
            match block {
                Block::Section(section) => {
                    for binder in &section.params {
                        term_indirect_externals(&binder.ty, closure, out);
                    }
                    walk_blocks(&section.blocks, closure, out);
                }
                Block::Declaration(declaration) => {
                    for binder in &declaration.params {
                        term_indirect_externals(&binder.ty, closure, out);
                    }
                    match &declaration.body {
                        DeclBody::TheoremLike { statement, proof } => {
                            term_indirect_externals(statement, closure, out);
                            proof_indirect_externals(proof, closure, out);
                        }
                        DeclBody::Definition { ty, value, .. } => {
                            term_indirect_externals(ty, closure, out);
                            term_indirect_externals(value, closure, out);
                        }
                    }
                }
            }
        }
    }
    let mut out = BTreeMap::new();
    crate::link::collect_document_externals(document, &mut out);
    walk_blocks(&document.blocks, closure, &mut out);
    out
}

/// The sorted, deduplicated import list of one module (§18.3): the modules
/// of every reached external constant plus the full generated names of
/// document imports.
#[must_use]
pub fn module_imports(
    document: &DocumentModule,
    closure: &Closure,
    module_prefix: &str,
) -> Vec<String> {
    let mut imports: BTreeSet<String> = BTreeSet::new();
    for external in document_externals(document, closure).values() {
        imports.insert(external.lean_module.clone());
    }
    for import in &document.imports {
        imports.insert(format!("{module_prefix}.{import}"));
    }
    imports.into_iter().collect()
}

// ---------------------------------------------------------------------------
// Module rendering
// ---------------------------------------------------------------------------

/// The source-introduction range of every local in a module: the earliest
/// source coverage row bound to the local (§20.3, per-binder mappings).
fn binder_ranges(checked: &CheckedModule) -> BTreeMap<LocalId, (usize, usize)> {
    let mut out: BTreeMap<LocalId, (usize, usize)> = BTreeMap::new();
    for row in &checked.coverage_source {
        if let Origin::Local(id) = row.binding {
            let id = LocalId(id as u64);
            let range = (row.byte_start, row.byte_end);
            match out.get(&id) {
                Some(existing) if existing.0 <= range.0 => {}
                _ => {
                    out.insert(id, range);
                }
            }
        }
    }
    out
}

/// The declaration origin, or an internal error: no declaration may be
/// rendered without its source ranges (§20.3 forbids fabricated spans).
fn origin_of<'a>(
    checked: &'a CheckedModule,
    component: &str,
) -> Result<&'a DeclOrigin, Diagnostic> {
    checked
        .decl_origins
        .get(component)
        .ok_or_else(|| internal(format!("declaration `{component}` has no source origin")))
}

/// Render one module's canonical `.lean` (§18.1) through a tracing emitter.
#[allow(clippy::too_many_lines)]
pub fn render_module(
    checked: &CheckedModule,
    closure: &Closure,
    module_prefix: &str,
    aliases: &DocumentAliases<'_>,
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
            aliases,
        };
        sink.kw("module");
        sink.ws("\n");
        for import in module_imports(document, closure, module_prefix) {
            // Under the Lean 4.32.1 module system a plain `import` is
            // private: constants of the imported module may not appear in
            // the signatures of this module's `public` declarations. Every
            // generated declaration is public API, so every import is a
            // `public import` (README, documented deviations).
            sink.kw("public");
            sink.ws(" ");
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

    let binders = binder_ranges(checked);
    for declaration in document.declarations() {
        emitter.ws("\n");
        let origin = origin_of(checked, &declaration.component)?;
        render_declaration(
            &mut emitter,
            declaration,
            origin,
            &binders,
            document,
            closure,
            aliases,
        )?;
    }

    emitter.ws("\n");
    let end_node = emitter.node("lean-preamble");
    {
        let mut sink = Sink {
            emitter: &mut emitter,
            source: EmitSource::Synthetic("core:lean-preamble/1".to_owned()),
            role: MapRole::Synthetic,
            node: end_node,
            aliases,
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

/// Print one declaration parameter under the binder role, mapped to the
/// binder's own source introduction when one exists (a section parameter
/// or lifted universal binder), else to the statement sentence.
fn print_mapped_param(
    sink: &mut Sink<'_>,
    binder: &Binder,
    namer: &mut Namer,
    ctx: TermCtx<'_>,
    binders: &BTreeMap<LocalId, (usize, usize)>,
    sentence: (usize, usize),
) -> Result<(), Diagnostic> {
    let (start, end) = binders.get(&binder.id).copied().unwrap_or(sentence);
    sink.source = EmitSource::File(start, end);
    sink.role = MapRole::Binder;
    print_param(sink, binder, namer, ctx)
}

#[allow(clippy::too_many_lines)]
fn render_declaration(
    emitter: &mut Emitter,
    declaration: &Declaration,
    origin: &DeclOrigin,
    binders: &BTreeMap<LocalId, (usize, usize)>,
    document: &DocumentModule,
    closure: &Closure,
    aliases: &DocumentAliases<'_>,
) -> Result<(), Diagnostic> {
    let node = emitter.node("declaration");
    let ctx = TermCtx { closure };
    let mut namer = Namer::for_declaration(declaration, ctx);
    match &declaration.body {
        DeclBody::TheoremLike { statement, proof } => {
            let mut sink = Sink {
                emitter,
                source: EmitSource::File(origin.whole.0, origin.whole.1),
                role: MapRole::Declaration,
                node,
                aliases,
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
            for binder in &declaration.params {
                sink.ws(" ");
                print_mapped_param(&mut sink, binder, &mut namer, ctx, binders, origin.sentence)?;
            }
            let mut rest = statement.clone();
            loop {
                match rest {
                    Term::Pi {
                        binders: ref lifted,
                        ..
                    } if lifted.iter().all(|binder| !binder.spelling.is_empty()) => {
                        let Term::Pi {
                            binders: lifted,
                            body,
                        } = rest
                        else {
                            unreachable!("matched above");
                        };
                        for binder in &lifted {
                            sink.ws(" ");
                            print_mapped_param(
                                &mut sink,
                                binder,
                                &mut namer,
                                ctx,
                                binders,
                                origin.sentence,
                            )?;
                        }
                        rest = *body;
                    }
                    _ => break,
                }
            }
            sink.source = EmitSource::File(origin.sentence.0, origin.sentence.1);
            sink.role = MapRole::Term;
            sink.ws(" ");
            sink.sym(":");
            sink.ws(" ");
            print_term_expr(&mut sink, &rest, &mut namer, ctx)?;
            sink.ws(" ");
            sink.sym(":=");
            sink.ws(" ");
            sink.kw("by");
            sink.ws("\n");
            let proof_range = origin.proof.unwrap_or(origin.whole);
            sink.source = EmitSource::File(proof_range.0, proof_range.1);
            sink.role = MapRole::Proof;
            let mut cursor = StepCursor {
                steps: &origin.steps,
                next: 0,
            };
            print_proof(&mut sink, proof, &mut namer, ctx, 1, &mut cursor)?;
            if cursor.next != cursor.steps.len() {
                return Err(internal(format!(
                    "declaration `{}` has {} proof-step origins for {} printed steps",
                    declaration.component,
                    cursor.steps.len(),
                    cursor.next
                )));
            }
        }
        DeclBody::Definition { ty, value, .. } => {
            let mut sink = Sink {
                emitter,
                source: EmitSource::File(origin.whole.0, origin.whole.1),
                role: MapRole::Declaration,
                node,
                aliases,
            };
            // A document definition is a transparent, nonrecursive `def`
            // (§18.6). Under the Lean 4.32.1 module system a definition's
            // body is hidden from importing modules unless it is exposed, so
            // every generated definition is `@[expose] public def` (README,
            // documented deviations): a theorem in an importing module may
            // unfold it exactly as one in the defining module can.
            sink.sym("@[");
            sink.kw("expose");
            sink.sym("]");
            sink.ws(" ");
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
            for binder in &declaration.params {
                sink.ws(" ");
                print_mapped_param(&mut sink, binder, &mut namer, ctx, binders, origin.sentence)?;
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
                print_mapped_param(&mut sink, binder, &mut namer, ctx, binders, origin.sentence)?;
            }
            sink.source = EmitSource::File(origin.sentence.0, origin.sentence.1);
            sink.role = MapRole::Term;
            sink.ws(" ");
            sink.sym(":");
            sink.ws(" ");
            print_term_expr(&mut sink, &result_ty, &mut namer, ctx)?;
            sink.ws(" ");
            sink.sym(":=");
            sink.ws("\n");
            sink.ws("  ");
            print_term_expr(&mut sink, &body, &mut namer, ctx)?;
            sink.ws("\n");
        }
    }
    Ok(())
}

fn print_param(
    sink: &mut Sink<'_>,
    binder: &Binder,
    namer: &mut Namer,
    ctx: TermCtx<'_>,
) -> Result<(), Diagnostic> {
    let name = namer.term_binder(binder.id);
    print_binder_open(sink, binder.mode);
    sink.ident(&name, Origin::Local(binder.id.0 as usize));
    sink.ws(" ");
    sink.sym(":");
    sink.ws(" ");
    print_term(sink, &binder.ty, namer, ctx, false, false)?;
    print_binder_close(sink, binder.mode);
    Ok(())
}

// ---------------------------------------------------------------------------
// Probe and audit modules
// ---------------------------------------------------------------------------

/// One probe line's provenance: which entry produced which generated line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProbeLine {
    /// The one-based generated line number.
    pub line: usize,
    /// The probe entry index (the universe-prefix index).
    pub index: usize,
    /// The qualified entry ID.
    pub entry: String,
}

/// The generated probe module (§18.8).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProbeModule {
    /// The reserved module name.
    pub name: String,
    /// The module source.
    pub text: String,
    /// The `example` lines and their entries, in line order.
    pub lines: Vec<ProbeLine>,
    /// Entries imported but not probed because their descriptor carries no
    /// signature (a `cases`/`induction` constructor entry without one).
    pub unprobed: Vec<String>,
}

impl ProbeModule {
    /// The entries whose `example` lines include the given one-based
    /// generated line, for failure attribution.
    #[must_use]
    pub fn entry_at_line(&self, line: usize) -> Option<&ProbeLine> {
        self.lines.iter().find(|row| row.line == line)
    }
}

/// The probe module source (§18.8): every used external Lean entry, sorted
/// by qualified entry ID, as `example : <signature> := <constant>`, with
/// universe variables alpha-renamed under an entry-index prefix and
/// declared through one `universe` command (Lean 4 has no `example.{u}`
/// form). Constructor entries reached through `cases`/`induction` are
/// probed like any other external when the descriptor's entry carries a
/// signature; a signature-less entry is imported only and listed in
/// `unprobed`.
pub fn probe_module(
    semantic_hex32: &str,
    externals: &BTreeMap<String, ExternalConstRef>,
    closure: &Closure,
) -> Result<ProbeModule, Diagnostic> {
    let name = format!("LexLeanProbe.P{semantic_hex32}");
    let mut imports: BTreeSet<String> = BTreeSet::new();
    for external in externals.values() {
        imports.insert(external.lean_module.clone());
    }
    let mut examples: Vec<(usize, String, String)> = Vec::new();
    let mut universes: Vec<String> = Vec::new();
    let mut unprobed = Vec::new();
    for (index, (entry_id, external)) in externals.iter().enumerate() {
        let qualified = qualified_of(entry_id)?;
        let entry = closure.entry(&qualified).ok_or_else(|| {
            Diagnostic::new(code!("LLB6001"), format!("`{qualified}` is unavailable"))
        })?;
        let Some(signature) = entry.signature.as_ref() else {
            unprobed.push(entry_id.clone());
            continue;
        };
        let prefix = format!("p{index}");
        for universe in &entry.universes {
            let renamed = format!("{prefix}{universe}");
            if !universes.contains(&renamed) {
                universes.push(renamed);
            }
        }
        collect_universe_vars(signature, &prefix, &mut universes);
        let ty = print_lse_type(signature, closure, &prefix)?;
        examples.push((
            index,
            entry_id.clone(),
            format!("example : {ty} := {}", external.lean_name),
        ));
    }
    let mut text = String::from("module\n");
    let mut line_count = 1usize;
    for import in &imports {
        text.push_str(&format!("import {import}\n"));
        line_count += 1;
    }
    text.push_str("set_option autoImplicit false\n");
    line_count += 1;
    if !universes.is_empty() {
        text.push_str(&format!("universe {}\n", universes.join(" ")));
        line_count += 1;
    }
    let mut lines = Vec::new();
    for (index, entry, example) in examples {
        line_count += 1;
        lines.push(ProbeLine {
            line: line_count,
            index,
            entry,
        });
        text.push_str(&example);
        text.push('\n');
    }
    Ok(ProbeModule {
        name,
        text,
        lines,
        unprobed,
    })
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
