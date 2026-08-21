//! Document IR (SPEC.md §17.5): modules, sections, phrases, and the linked
//! project.

use std::collections::BTreeMap;

use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::Sha256Digest;
use crate::ir::core::CoreModule;
use crate::ir::declaration::Declaration;
use crate::ir::term::{Binder, Renumber, Term};
use crate::lexicon::lse::QualifiedId;

/// One item of a title or heading phrase (§15.3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PhraseItem {
    /// A glossary word: label-word, type-noun, or the canonical nominal form
    /// of a term or function entry.
    Word {
        /// The selected entry.
        entry: QualifiedId,
        /// The selected form ID.
        form: String,
    },
    /// A non-`Prop` mathematical term.
    Math(Term),
    /// Core phrase punctuation: `:`, `-`, `(`, or `)`.
    Punctuation(QualifiedId),
}

/// A bounded concept phrase.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Phrase {
    /// The items in order.
    pub items: Vec<PhraseItem>,
}

impl Phrase {
    /// Canonical JSON.
    #[must_use]
    pub fn to_json(&self, renumber: &mut Renumber) -> Json {
        Json::Arr(
            self.items
                .iter()
                .map(|item| match item {
                    PhraseItem::Word { entry, form } => Json::object(vec![
                        ("k", Json::Str("word".to_owned())),
                        ("entry", Json::Str(entry.to_string())),
                        ("form", Json::Str(form.clone())),
                    ]),
                    PhraseItem::Math(term) => Json::object(vec![
                        ("k", Json::Str("math".to_owned())),
                        ("t", term.to_json(renumber)),
                    ]),
                    PhraseItem::Punctuation(entry) => Json::object(vec![
                        ("k", Json::Str("punct".to_owned())),
                        ("entry", Json::Str(entry.to_string())),
                    ]),
                })
                .collect(),
        )
    }
}

/// One block: a section or a declaration, in source order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Block {
    /// A section.
    Section(Section),
    /// A declaration.
    Declaration(Box<Declaration>),
}

/// One section (§15.1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Section {
    /// The component ID.
    pub component: String,
    /// The heading phrase.
    pub heading: Phrase,
    /// Explicit section parameters.
    pub params: Vec<Binder>,
    /// Nested blocks in source order.
    pub blocks: Vec<Block>,
}

/// One linked document module (§17.5).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocumentModule {
    /// The source module name, e.g. `Main`.
    pub name: String,
    /// The full generated Lean module name.
    pub lean_module: String,
    /// The project-relative source path.
    pub source_path: String,
    /// SHA-256 of the normalized source.
    pub source_sha256: Sha256Digest,
    /// Used glossary packages, `package@version`, sorted.
    pub glossary: Vec<String>,
    /// Explicit module imports, sorted.
    pub imports: Vec<String>,
    /// The title phrase.
    pub title: Phrase,
    /// Top-level blocks in source order.
    pub blocks: Vec<Block>,
    /// A closed kernel module, exclusively present when `blocks` is empty.
    pub core: Option<CoreModule>,
}

impl DocumentModule {
    /// Every declaration in source order, with its inherited-parameter
    /// context flattened by the linker.
    #[must_use]
    pub fn declarations(&self) -> Vec<&Declaration> {
        fn walk<'ir>(blocks: &'ir [Block], out: &mut Vec<&'ir Declaration>) {
            for block in blocks {
                match block {
                    Block::Declaration(declaration) => out.push(declaration),
                    Block::Section(section) => walk(&section.blocks, out),
                }
            }
        }
        let mut out = Vec::new();
        walk(&self.blocks, &mut out);
        out
    }

    /// Canonical JSON (§17.9), alpha-safe.
    #[must_use]
    pub fn to_json(&self) -> Json {
        fn block_json(block: &Block, renumber: &mut Renumber) -> Json {
            match block {
                Block::Declaration(declaration) => Json::object(vec![
                    ("k", Json::Str("declaration".to_owned())),
                    ("d", declaration.to_json(renumber)),
                ]),
                Block::Section(section) => {
                    let heading = section.heading.to_json(renumber);
                    let params: Vec<Json> = section
                        .params
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
                        ("k", Json::Str("section".to_owned())),
                        ("component", Json::Str(section.component.clone())),
                        ("heading", heading),
                        ("params", Json::Arr(params)),
                        (
                            "blocks",
                            Json::Arr(
                                section
                                    .blocks
                                    .iter()
                                    .map(|inner| block_json(inner, renumber))
                                    .collect(),
                            ),
                        ),
                    ])
                }
            }
        }
        let mut renumber = Renumber::default();
        let mut fields = vec![
            ("name", Json::Str(self.name.clone())),
            ("lean_module", Json::Str(self.lean_module.clone())),
            (
                "glossary",
                Json::Arr(self.glossary.iter().cloned().map(Json::Str).collect()),
            ),
            (
                "imports",
                Json::Arr(self.imports.iter().cloned().map(Json::Str).collect()),
            ),
            ("title", self.title.to_json(&mut renumber)),
            (
                "blocks",
                Json::Arr(
                    self.blocks
                        .iter()
                        .map(|block| block_json(block, &mut renumber))
                        .collect(),
                ),
            ),
        ];
        if let Some(core) = &self.core {
            fields.push((
                "core",
                Json::Str(serde_json::to_string(core).unwrap_or_default()),
            ));
        }
        Json::object(fields)
    }
}

/// A linked project: a sorted map of module name to module (§17.5).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LinkedProject {
    /// Modules by name.
    pub modules: BTreeMap<String, DocumentModule>,
}

impl LinkedProject {
    /// The canonical linked-IR JSON hashed into the semantic ID (§21.4).
    #[must_use]
    pub fn to_json(&self) -> Json {
        Json::object(vec![
            ("spec", Json::Str("lexlean/linked-ir/1".to_owned())),
            (
                "modules",
                Json::Arr(self.modules.values().map(DocumentModule::to_json).collect()),
            ),
        ])
    }

    /// A declaration by module and component.
    #[must_use]
    pub fn declaration(&self, module: &str, component: &str) -> Option<&Declaration> {
        self.modules.get(module).and_then(|document| {
            document
                .declarations()
                .into_iter()
                .find(|declaration| declaration.component == component)
        })
    }
}
