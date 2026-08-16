//! Term IR (SPEC.md §17.2, §17.3).

use std::collections::BTreeMap;

use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::Sha256Digest;
pub use crate::lexicon::lse::{BinderMode, Universe};

/// An opaque monotonically assigned local identity, unique within one linked
/// project (§17.2). Display spellings are metadata, not identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalId(pub u64);

/// A qualified package identifier.
pub type QualifiedPackageId = String;
/// A qualified entry identifier, `package::entry`.
pub type QualifiedEntryId = String;
/// A Lean module name.
pub type LeanModuleName = String;
/// A fully qualified Lean name.
pub type LeanName = String;

/// The closed core constructors that can appear in term position. Every
/// logical surface construct desugars to an application of one of these or
/// to a `Pi` (implication and universal quantification).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CoreRef {
    /// `Eq`.
    Eq,
    /// `And`.
    And,
    /// `Or`.
    Or,
    /// `Not`.
    Not,
    /// `Iff`.
    Iff,
    /// `Exists`.
    Exists,
    /// `ExistsUnique`.
    ExistsUnique,
}

impl CoreRef {
    /// The core constructor name in glossary data, e.g. `logic.eq`.
    #[must_use]
    pub fn from_constructor(constructor: &str) -> Option<Self> {
        Some(match constructor {
            "logic.eq" => Self::Eq,
            "logic.and" => Self::And,
            "logic.or" => Self::Or,
            "logic.not" => Self::Not,
            "logic.iff" => Self::Iff,
            "logic.exists" => Self::Exists,
            "logic.exists-unique" => Self::ExistsUnique,
            _ => return None,
        })
    }

    /// The fully qualified Lean lowering (§18.4).
    #[must_use]
    pub const fn lean_name(self) -> &'static str {
        match self {
            Self::Eq => "Eq",
            Self::And => "And",
            Self::Or => "Or",
            Self::Not => "Not",
            Self::Iff => "Iff",
            Self::Exists => "Exists",
            Self::ExistsUnique => "ExistsUnique",
        }
    }

    /// The stable serialization tag.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Eq => "eq",
            Self::And => "and",
            Self::Or => "or",
            Self::Not => "not",
            Self::Iff => "iff",
            Self::Exists => "exists",
            Self::ExistsUnique => "exists-unique",
        }
    }
}

/// An external Lean constant reference (§17.2).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExternalConstRef {
    /// The declaring package.
    pub package: QualifiedPackageId,
    /// The qualified entry.
    pub entry: QualifiedEntryId,
    /// The Lean module to import.
    pub lean_module: LeanModuleName,
    /// The fully qualified Lean name.
    pub lean_name: LeanName,
    /// The canonical signature hash.
    pub signature_hash: Sha256Digest,
}

/// A document declaration reference (§17.2).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DocumentDeclRef {
    /// The logical source module.
    pub module: String,
    /// The component ID.
    pub component: String,
    /// The linked full generated Lean name.
    pub lean_name: LeanName,
}

/// A defined lexicon value reference (§17.2). Its value is inlined at
/// lowering; the reference keeps the identity.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DefinedLexiconRef {
    /// The declaring package.
    pub package: QualifiedPackageId,
    /// The qualified entry.
    pub entry: QualifiedEntryId,
    /// The canonical signature hash.
    pub signature_hash: Sha256Digest,
}

/// A global reference (§17.2), exactly.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum GlobalRef {
    /// A core constructor.
    Core(CoreRef),
    /// An external Lean constant.
    External(ExternalConstRef),
    /// A document declaration.
    Document(DocumentDeclRef),
    /// A defined lexicon value.
    DefinedLexicon(DefinedLexiconRef),
}

/// The index of an omitted implicit binder within the applied signature's
/// binder list (§17.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ImplicitBinderId(pub u32);

/// One typed binder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binder {
    /// The capture-free identity (I9).
    pub id: LocalId,
    /// Explicit, implicit, or instance.
    pub mode: BinderMode,
    /// The binder type.
    pub ty: Term,
    /// The display spelling, metadata only.
    pub spelling: String,
}

/// The closed term IR (§17.3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// A sort.
    Sort(Universe),
    /// A local occurrence.
    Local(LocalId),
    /// A global with instantiated universe arguments.
    Global(GlobalRef, Vec<Universe>),
    /// A controlled application.
    App {
        /// The applied function.
        function: Box<Term>,
        /// The explicit arguments.
        explicit_args: Vec<Term>,
        /// Implicit binders of the applied signature that elaboration
        /// solved and omitted (§17.6).
        omitted_implicit_binders: Vec<ImplicitBinderId>,
    },
    /// A dependent function type.
    Pi {
        /// The binders.
        binders: Vec<Binder>,
        /// The body.
        body: Box<Term>,
    },
    /// A lambda.
    Lambda {
        /// The binders.
        binders: Vec<Binder>,
        /// The body.
        body: Box<Term>,
    },
    /// A let binding. The binder is boxed only to give the recursive type a
    /// finite size; the represented shape is §17.3's `binder: Binder`.
    Let {
        /// The binder.
        binder: Box<Binder>,
        /// Its value.
        value: Box<Term>,
        /// The body.
        body: Box<Term>,
    },
    /// A numeral with its uniquely determined expected type (§15.5).
    NatLiteral {
        /// The decimal spelling.
        decimal: String,
        /// The expected type.
        expected_type: Box<Term>,
    },
}

/// The sort `Prop`.
#[must_use]
pub fn prop() -> Term {
    Term::Sort(Universe::Num(0))
}

/// Is this term literally the sort `Prop`?
#[must_use]
pub fn is_prop(term: &Term) -> bool {
    matches!(term, Term::Sort(Universe::Num(0)))
}

fn universe_json(universe: &Universe) -> Json {
    match universe {
        Universe::Num(n) => Json::object(vec![(
            "num",
            Json::Int(i64::try_from(*n).unwrap_or(i64::MAX)),
        )]),
        Universe::Var(name) => Json::object(vec![("var", Json::Str(name.clone()))]),
        Universe::Succ(inner) => Json::object(vec![("succ", universe_json(inner))]),
        Universe::Max(items) => Json::object(vec![(
            "max",
            Json::Arr(items.iter().map(universe_json).collect()),
        )]),
        Universe::IMax(a, b) => Json::object(vec![(
            "imax",
            Json::Arr(vec![universe_json(a), universe_json(b)]),
        )]),
    }
}

fn global_json(global: &GlobalRef) -> Json {
    match global {
        GlobalRef::Core(core) => Json::object(vec![
            ("kind", Json::Str("core".to_owned())),
            ("name", Json::Str(core.as_str().to_owned())),
        ]),
        GlobalRef::External(external) => Json::object(vec![
            ("kind", Json::Str("external".to_owned())),
            ("entry", Json::Str(external.entry.clone())),
            ("lean_module", Json::Str(external.lean_module.clone())),
            ("lean_name", Json::Str(external.lean_name.clone())),
            (
                "signature_sha256",
                Json::Str(external.signature_hash.to_hex()),
            ),
        ]),
        GlobalRef::Document(document) => Json::object(vec![
            ("kind", Json::Str("document".to_owned())),
            ("module", Json::Str(document.module.clone())),
            ("component", Json::Str(document.component.clone())),
            ("lean_name", Json::Str(document.lean_name.clone())),
        ]),
        GlobalRef::DefinedLexicon(defined) => Json::object(vec![
            ("kind", Json::Str("defined".to_owned())),
            ("entry", Json::Str(defined.entry.clone())),
            (
                "signature_sha256",
                Json::Str(defined.signature_hash.to_hex()),
            ),
        ]),
    }
}

impl Term {
    /// Canonical, alpha-safe JSON (§17.9): locals serialize as dense indices
    /// assigned in traversal order, so identical structure serializes
    /// identically whatever `LocalId`s elaboration allocated.
    #[must_use]
    pub fn to_json(&self, renumber: &mut Renumber) -> Json {
        match self {
            Self::Sort(universe) => Json::object(vec![
                ("k", Json::Str("sort".to_owned())),
                ("u", universe_json(universe)),
            ]),
            Self::Local(id) => match renumber.resolve(*id) {
                Resolved::Bound(index) => Json::object(vec![
                    ("k", Json::Str("local".to_owned())),
                    ("id", Json::from_usize(index)),
                ]),
                Resolved::Free(free) => Json::object(vec![
                    ("k", Json::Str("local".to_owned())),
                    (
                        "free",
                        Json::Int(i64::try_from(free.0).unwrap_or(i64::MAX)),
                    ),
                ]),
            },
            Self::Global(global, universes) => {
                let mut fields = vec![
                    ("k", Json::Str("global".to_owned())),
                    ("g", global_json(global)),
                ];
                if !universes.is_empty() {
                    fields.push((
                        "u",
                        Json::Arr(universes.iter().map(universe_json).collect()),
                    ));
                }
                Json::object(fields)
            }
            Self::App {
                function,
                explicit_args,
                omitted_implicit_binders,
            } => {
                let mut fields = vec![
                    ("k", Json::Str("app".to_owned())),
                    ("f", function.to_json(renumber)),
                    (
                        "a",
                        Json::Arr(
                            explicit_args
                                .iter()
                                .map(|arg| arg.to_json(renumber))
                                .collect(),
                        ),
                    ),
                ];
                if !omitted_implicit_binders.is_empty() {
                    fields.push((
                        "i",
                        Json::Arr(
                            omitted_implicit_binders
                                .iter()
                                .map(|binder| Json::from_usize(binder.0 as usize))
                                .collect(),
                        ),
                    ));
                }
                Json::object(fields)
            }
            Self::Pi { binders, body } | Self::Lambda { binders, body } => {
                let tag = if matches!(self, Self::Pi { .. }) {
                    "pi"
                } else {
                    "lam"
                };
                let binder_json: Vec<Json> = binders
                    .iter()
                    .map(|binder| {
                        let ty = binder.ty.to_json(renumber);
                        let index = renumber.bind(binder.id);
                        Json::object(vec![
                            ("id", Json::from_usize(index)),
                            ("m", Json::Str(binder.mode.as_str().to_owned())),
                            ("s", Json::Str(binder.spelling.clone())),
                            ("t", ty),
                        ])
                    })
                    .collect();
                Json::object(vec![
                    ("k", Json::Str(tag.to_owned())),
                    ("b", Json::Arr(binder_json)),
                    ("v", body.to_json(renumber)),
                ])
            }
            Self::Let {
                binder,
                value,
                body,
            } => {
                let ty = binder.ty.to_json(renumber);
                let value_json = value.to_json(renumber);
                let index = renumber.bind(binder.id);
                Json::object(vec![
                    ("k", Json::Str("let".to_owned())),
                    (
                        "b",
                        Json::object(vec![
                            ("id", Json::from_usize(index)),
                            ("m", Json::Str(binder.mode.as_str().to_owned())),
                            ("s", Json::Str(binder.spelling.clone())),
                            ("t", ty),
                        ]),
                    ),
                    ("x", value_json),
                    ("v", body.to_json(renumber)),
                ])
            }
            Self::NatLiteral {
                decimal,
                expected_type,
            } => Json::object(vec![
                ("k", Json::Str("nat".to_owned())),
                ("d", Json::Str(decimal.clone())),
                ("t", expected_type.to_json(renumber)),
            ]),
        }
    }

    /// The alpha-safe canonical key used for hashing and serialization
    /// (§17.9). Display spellings are excluded. Two terms that differ only
    /// in which free locals they mention share one key, so this key is
    /// never used to decide equality of terms inside one scope; see
    /// [`Term::eq_key`].
    #[must_use]
    pub fn canonical_key(&self) -> String {
        Self::strip_spellings(&self.to_json(&mut Renumber::default())).to_canonical_string()
    }

    /// The comparison key used wherever two terms of one scope are compared
    /// for equality (residual premises, calculation endpoints, definition
    /// binder types, alternative collapse; §14.4, §16.10): bound binders
    /// are renumbered so alpha-renaming is invisible, and free locals keep
    /// their `LocalId` verbatim so distinct locals never conflate.
    #[must_use]
    pub fn eq_key(&self) -> String {
        Self::strip_spellings(&self.to_json(&mut Renumber::keeping_free()))
            .to_canonical_string()
    }

    /// The nesting depth of a term, computed without recursion so a deep
    /// term can be measured before any recursive walker touches it
    /// (§25.5). A leaf has depth 1.
    #[must_use]
    pub fn depth(&self) -> u64 {
        let mut max_depth: u64 = 0;
        let mut stack: Vec<(&Term, u64)> = vec![(self, 1)];
        while let Some((term, depth)) = stack.pop() {
            max_depth = max_depth.max(depth);
            let next = depth.saturating_add(1);
            match term {
                Self::Sort(_) | Self::Local(_) | Self::Global(..) => {}
                Self::App {
                    function,
                    explicit_args,
                    ..
                } => {
                    stack.push((function, next));
                    for argument in explicit_args {
                        stack.push((argument, next));
                    }
                }
                Self::Pi { binders, body } | Self::Lambda { binders, body } => {
                    for binder in binders {
                        stack.push((&binder.ty, next));
                    }
                    stack.push((body, next));
                }
                Self::Let {
                    binder,
                    value,
                    body,
                } => {
                    stack.push((&binder.ty, next));
                    stack.push((value, next));
                    stack.push((body, next));
                }
                Self::NatLiteral { expected_type, .. } => stack.push((expected_type, next)),
            }
        }
        max_depth
    }

    fn strip_spellings(json: &Json) -> Json {
        fn strip(json: &Json) -> Json {
            match json {
                Json::Obj(object) => Json::Obj(
                    object
                        .iter()
                        .filter(|(key, _)| key.as_str() != "s")
                        .map(|(key, value)| (key.clone(), strip(value)))
                        .collect(),
                ),
                Json::Arr(items) => Json::Arr(items.iter().map(strip).collect()),
                other => other.clone(),
            }
        }
        strip(json)
    }
}

/// One resolved local occurrence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Resolved {
    /// A binder-bound (or, under the hashing renumbering, first-seen)
    /// local, as its dense index.
    Bound(usize),
    /// A free local kept verbatim (comparison renumbering only).
    Free(LocalId),
}

/// Dense renumbering of `LocalId`s in traversal order, for alpha-safe
/// serialization.
#[derive(Debug, Default)]
pub struct Renumber {
    map: BTreeMap<LocalId, usize>,
    keep_free: bool,
}

impl Renumber {
    /// A renumbering that keeps free locals verbatim (comparison keys).
    #[must_use]
    pub fn keeping_free() -> Self {
        Self {
            map: BTreeMap::new(),
            keep_free: true,
        }
    }

    /// Assign the next dense index to a binder.
    pub fn bind(&mut self, id: LocalId) -> usize {
        let next = self.map.len();
        *self.map.entry(id).or_insert(next)
    }

    /// Resolve an occurrence. Under the hashing renumbering, free locals
    /// (section parameters serialized at declaration scope) enter the
    /// numbering on first use; under the comparison renumbering they stay
    /// verbatim.
    pub fn resolve(&mut self, id: LocalId) -> Resolved {
        if let Some(index) = self.map.get(&id) {
            return Resolved::Bound(*index);
        }
        if self.keep_free {
            return Resolved::Free(id);
        }
        let next = self.map.len();
        self.map.insert(id, next);
        Resolved::Bound(next)
    }
}
