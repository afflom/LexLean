//! Linking (SPEC.md §17.1 phases 4–15): normalize, scan, parse, elaborate,
//! and link every selected module and its transitive import closure into
//! one `LinkedProject`, with complete source coverage and content IDs. No
//! backend runs before linked IR is complete.

use std::collections::{BTreeMap, BTreeSet};

use crate::artifact::content_id::{self, Sha256Digest};
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::elaborate::definitions::elab_definition;
use crate::elaborate::expressions::lse_to_term;
use crate::elaborate::proofs::ProofElab;
use crate::elaborate::resolve::{LocalAlloc, ScopeStack};
use crate::elaborate::{
    elab_binder, elab_island, elab_proposition_sentence, DeclInfo, DeclTable, Shared,
};
use crate::error::LexLeanError;
use crate::grammar::chart::{text_tokens, Budget, TextToken};
use crate::grammar::proposition::{parse_phrase, PhraseItemAst, TextParser};
use crate::grammar::structural::{self, AtomRange, BlockAst, DeclAst, ModuleAst, PolicyKind};
use crate::ir::declaration::{AxiomPolicy, DeclBody, Declaration};
use crate::ir::document::{Block, DocumentModule, LinkedProject, Phrase, PhraseItem, Section};
use crate::ir::proof::{CaseProof, Proof};
use crate::ir::term::{Binder, ExternalConstRef, GlobalRef, LocalId, Term};
use crate::lexicon::lse::QualifiedId;
use crate::lexicon::package::{LexiconPackage, PackageRef};
use crate::lexicon::resolve::Closure;
use crate::lock::Lock;
use crate::project::{Project, Selection};
use crate::source::atom::{Atom, AtomClass};
use crate::source::coverage::{Coverage, Origin, SourceRow};

/// Byte-range origins of one declaration in its module source (for source
/// maps, §20.3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclOrigin {
    /// The whole environment.
    pub whole: (usize, usize),
    /// The proposition or definition sentence, period included.
    pub sentence: (usize, usize),
    /// The proof environment, when theorem-like.
    pub proof: Option<(usize, usize)>,
}

/// One fully checked module.
#[derive(Debug)]
pub struct CheckedModule {
    /// The linked document.
    pub document: DocumentModule,
    /// The normalized source text.
    pub normalized: String,
    /// The scanned atoms.
    pub atoms: Vec<Atom>,
    /// Source coverage rows, sorted and closure-checked.
    pub coverage_source: Vec<SourceRow>,
    /// Declaration origins by component.
    pub decl_origins: BTreeMap<String, DeclOrigin>,
    /// The packages visible to this module.
    pub visible: BTreeSet<String>,
    /// Display spellings of proof-introduced locals (for canonical
    /// formatting and rendering).
    pub proof_spellings: BTreeMap<LocalId, String>,
}

/// The result of `check`: everything the backends and verification need.
pub struct CheckedProject {
    /// Checked modules by name.
    pub modules: BTreeMap<String, CheckedModule>,
    /// The linked project IR.
    pub linked: LinkedProject,
    /// The glossary closure.
    pub closure: Closure,
    /// The union of visible packages across modules.
    pub visible_union: BTreeSet<String>,
    /// Every used external Lean entry, sorted by qualified entry ID (for
    /// the probe module, §18.8).
    pub external_used: BTreeMap<String, ExternalConstRef>,
    /// The source ID (§21.3).
    pub source_id: Sha256Digest,
    /// The semantic ID (§21.4).
    pub semantic_id: Sha256Digest,
    /// The canonical lock bytes hashed into the source ID.
    pub canonical_lock: Vec<u8>,
}

fn err(diagnostics: Vec<Diagnostic>) -> LexLeanError {
    LexLeanError::from_diagnostics(diagnostics)
}

fn bytes_of(atoms: &[Atom], range: AtomRange) -> (usize, usize) {
    if range.0 >= atoms.len() {
        return (0, 0);
    }
    let first = &atoms[range.0];
    let last = &atoms[range.1.saturating_sub(1).max(range.0)];
    (first.byte_start, last.byte_end)
}

/// The conservative Lean keyword set for generated-name collision checks
/// (§17.8). Component IDs are lowercase, so only lowercase keywords matter.
const LEAN_KEYWORDS: [&str; 30] = [
    "apply",
    "at",
    "axiom",
    "by",
    "calc",
    "cases",
    "constructor",
    "def",
    "do",
    "else",
    "end",
    "exact",
    "example",
    "fun",
    "have",
    "if",
    "import",
    "in",
    "induction",
    "intro",
    "left",
    "let",
    "match",
    "module",
    "namespace",
    "open",
    "rfl",
    "right",
    "theorem",
    "with",
];

struct ModuleLoad {
    path: String,
    normalized: String,
    atoms: Vec<Atom>,
    ast: ModuleAst,
}

/// Run the complete check pipeline for a selection.
#[allow(clippy::too_many_lines)]
pub fn check_project(
    project: &Project,
    selection: &Selection,
    lock: &Lock,
    packages: Vec<LexiconPackage>,
) -> Result<CheckedProject, LexLeanError> {
    let limits = project.config.limits;
    let registry =
        crate::lexicon::load_token_registry().map_err(|diagnostic| err(vec![diagnostic]))?;
    let bootstrap = crate::lexicon::load_bootstrap().map_err(|diagnostic| err(vec![diagnostic]))?;
    let closure =
        Closure::build(packages, registry, bootstrap, limits.max_import_depth).map_err(err)?;

    // The explicit total-source budget counts configuration, lock, lexicon
    // manifests and entries, and normalized selected modules (§10.2).
    let mut total_bytes: u64 = project.config_bytes.len() as u64;
    let canonical_lock = lock.canonical_bytes();
    total_bytes = total_bytes.saturating_add(canonical_lock.len() as u64);
    for package in &closure.packages {
        total_bytes = total_bytes.saturating_add(package.total_bytes as u64);
    }
    let over_total = |total: u64| -> Option<LexLeanError> {
        if total > limits.max_total_source_bytes {
            Some(err(vec![Diagnostic::new(
                code!("LLS8002"),
                format!(
                    "max_total_source_bytes exceeded: configured {}, observed {total}",
                    limits.max_total_source_bytes
                ),
            )]))
        } else {
            None
        }
    };
    if let Some(error) = over_total(total_bytes) {
        return Err(error);
    }

    // Load the selection, then the transitive import closure (§15.1).
    let all_modules = project.all_modules().map_err(err)?;
    let selected = project.resolve_selection(selection).map_err(err)?;
    let mut loaded: BTreeMap<String, ModuleLoad> = BTreeMap::new();
    let mut worklist: Vec<(String, String)> = selected
        .iter()
        .map(|(module, path)| (module.clone(), path.clone()))
        .collect();
    while let Some((module_name, relative)) = worklist.pop() {
        if loaded.contains_key(&module_name) {
            continue;
        }
        let absolute = project
            .confined_file(&relative)
            .map_err(|diagnostic| err(vec![diagnostic]))?;
        let bytes = std::fs::read(absolute.as_std_path()).map_err(|io_error| {
            err(vec![Diagnostic::new(
                code!("LLS8001"),
                format!("{relative}: {io_error}"),
            )])
        })?;
        if bytes.len() as u64 > limits.max_file_bytes {
            return Err(err(vec![Diagnostic::new(
                code!("LLS8002"),
                format!(
                    "max_file_bytes exceeded: configured {}, observed {} in {relative}",
                    limits.max_file_bytes,
                    bytes.len()
                ),
            )]));
        }
        let normalized = crate::source::normalize::normalize(&relative, &bytes, false)
            .map_err(err)?
            .text;
        total_bytes = total_bytes.saturating_add(normalized.len() as u64);
        if let Some(error) = over_total(total_bytes) {
            return Err(error);
        }
        let atoms = crate::source::scan::scan(&relative, &normalized, limits.max_primitive_atoms)
            .map_err(|diagnostic| err(vec![diagnostic]))?;
        crate::source::scan::reject_forbidden_atoms(
            &relative,
            &atoms,
            &closure.bootstrap.structural.forbidden_controls,
        )
        .map_err(|diagnostic| err(vec![diagnostic]))?;
        let ast = structural::parse_module(&relative, &atoms, &module_name, limits.max_scope_depth)
            .map_err(|diagnostic| err(vec![diagnostic]))?;
        for import in &ast.imports {
            let import_name = import.text.clone();
            if import_name == module_name {
                return Err(err(vec![Diagnostic::new(
                    code!("LLR3003"),
                    format!("module `{module_name}` imports itself"),
                )]));
            }
            if !loaded.contains_key(&import_name) {
                match all_modules.get(&import_name) {
                    Some(import_path) => {
                        worklist.push((import_name, import_path.clone()));
                    }
                    None => {
                        return Err(err(vec![Diagnostic::new(
                            code!("LLR3005"),
                            format!(
                                "`{module_name}` imports `{import_name}`, which is not a project module"
                            ),
                        )]));
                    }
                }
            }
        }
        loaded.insert(
            module_name,
            ModuleLoad {
                path: relative,
                normalized,
                atoms,
                ast,
            },
        );
    }

    // Topological order over module imports; a cycle is LLR3003 (§15.1).
    let order = topo_order(&loaded).map_err(|cycle| {
        err(vec![Diagnostic::new(
            code!("LLR3003"),
            format!("module import cycle through `{cycle}`"),
        )])
    })?;

    let mut alloc = LocalAlloc::default();
    let mut decls = DeclTable::default();
    let mut modules: BTreeMap<String, CheckedModule> = BTreeMap::new();
    let mut visible_union: BTreeSet<String> = BTreeSet::new();
    let mut ir_node_count: u64 = 0;

    for module_name in &order {
        let load = &loaded[module_name];
        let mut budget = Budget::new(limits.max_token_lattice_edges, limits.max_parse_states);

        // Glossary uses: exact `package@version` rows matching the lock and
        // the loaded closure (§15.1, LLR3001).
        let mut used_ids: Vec<String> = Vec::new();
        let mut glossary: Vec<String> = Vec::new();
        for use_arg in &load.ast.uses {
            let reference = PackageRef::parse(&use_arg.text)
                .map_err(|reason| err(vec![Diagnostic::new(code!("LLR3001"), reason)]))?;
            match closure.package(&reference.package) {
                Some(package) if package.version == reference.version => {}
                Some(package) => {
                    return Err(err(vec![Diagnostic::new(
                        code!("LLR3001"),
                        format!(
                            "`{reference}` does not match the locked version {}",
                            package.version
                        ),
                    )]));
                }
                None => {
                    return Err(err(vec![Diagnostic::new(
                        code!("LLR3001"),
                        format!("`{reference}` is not in the locked closure"),
                    )]));
                }
            }
            if glossary.contains(&use_arg.text) {
                return Err(err(vec![Diagnostic::new(
                    code!("LLP2003"),
                    format!("duplicate \\useglossary{{{}}}", use_arg.text),
                )]));
            }
            glossary.push(use_arg.text.clone());
            used_ids.push(reference.package.clone());
        }
        glossary.sort();
        let visible = closure.visible_set(&used_ids);
        visible_union.extend(visible.iter().cloned());

        // Module imports: sorted, unique, direct-availability (§15.1, §17.7).
        let mut imports: Vec<String> = Vec::new();
        for import in &load.ast.imports {
            if imports.contains(&import.text) {
                return Err(err(vec![Diagnostic::new(
                    code!("LLP2003"),
                    format!("duplicate \\importmodule{{{}}}", import.text),
                )]));
            }
            imports.push(import.text.clone());
        }
        imports.sort();

        // The declarations visible to this module: its direct imports'
        // declarations, in availability order; its own grow as blocks link.
        let mut module_decls = DeclTable::default();
        for row in &decls.rows {
            if imports.contains(&row.module) {
                module_decls.rows.push(row.clone());
            }
        }

        let lean_module = format!("{}.{}", project.config.module_prefix, module_name);
        let mut rows: Vec<SourceRow> = load.ast.structural_rows.clone();
        let mut scopes = ScopeStack::default();
        scopes.push_frame();
        let mut components: BTreeSet<String> = BTreeSet::new();
        let mut lean_names: BTreeSet<String> = BTreeSet::new();
        let mut decl_origins: BTreeMap<String, DeclOrigin> = BTreeMap::new();
        let mut proof_spellings: BTreeMap<LocalId, String> = BTreeMap::new();

        // The title phrase (§15.3).
        let (title, title_rows) = {
            let shared = Shared {
                path: &load.path,
                atoms: &load.atoms,
                closure: &closure,
                visible: &visible,
                decls: &module_decls,
                module: module_name,
                module_prefix: &project.config.module_prefix,
            };
            elab_phrase(
                &shared,
                &mut scopes,
                &mut alloc,
                &mut budget,
                load.ast.title,
            )
            .map_err(|diagnostic| err(vec![diagnostic]))?
        };
        rows.extend(title_rows);

        // Blocks.
        let mut blocks: Vec<Block> = Vec::new();
        for block in &load.ast.blocks {
            let linked = link_block(
                project,
                &closure,
                &visible,
                &mut module_decls,
                &mut decls,
                module_name,
                &lean_module,
                load,
                &mut scopes,
                &mut alloc,
                &mut budget,
                &mut rows,
                &mut components,
                &mut lean_names,
                &mut decl_origins,
                &mut proof_spellings,
                block,
            )
            .map_err(|diagnostic| err(vec![diagnostic]))?;
            blocks.push(linked);
        }
        scopes.pop_frame();

        let document = DocumentModule {
            name: module_name.clone(),
            lean_module,
            source_path: load.path.clone(),
            source_sha256: Sha256Digest::of(load.normalized.as_bytes()),
            glossary,
            imports,
            title,
            blocks,
        };
        ir_node_count = ir_node_count.saturating_add(count_ir_nodes(&document));
        if ir_node_count > limits.max_ir_nodes {
            return Err(err(vec![Diagnostic::new(
                code!("LLS8002"),
                format!("max_ir_nodes exceeded: configured {}", limits.max_ir_nodes),
            )]));
        }

        // Coverage closure: every non-whitespace atom exactly once (I1).
        rows.sort_by_key(|a| (a.byte_start, a.byte_end));
        let coverage = Coverage {
            module: module_name.clone(),
            source: rows.clone(),
            latex: Vec::new(),
            lean: Vec::new(),
        };
        if let Err(reason) = coverage.check_source_closure(&load.path, &load.atoms) {
            return Err(err(vec![Diagnostic::new(code!("LLL1005"), reason)]));
        }

        modules.insert(
            module_name.clone(),
            CheckedModule {
                document,
                normalized: load.normalized.clone(),
                atoms: load.atoms.clone(),
                coverage_source: rows,
                decl_origins,
                visible,
                proof_spellings,
            },
        );
    }

    // Content identity (§21.3, §21.4).
    let linked = LinkedProject {
        modules: modules
            .iter()
            .map(|(name, module)| (name.clone(), module.document.clone()))
            .collect(),
    };
    let sources: Vec<(String, Vec<u8>)> = {
        let mut list: Vec<(String, Vec<u8>)> = loaded
            .values()
            .map(|load| (load.path.clone(), load.normalized.clone().into_bytes()))
            .collect();
        list.sort_by(|a, b| a.0.cmp(&b.0));
        list
    };
    let source_id = content_id::source_id(
        project.config.canonical_toml().as_bytes(),
        &canonical_lock,
        &sources,
    );
    let linked_ir_json = linked.to_json().to_canonical_string();
    let closure_json = closure
        .closure_json("", &visible_union)
        .to_canonical_string();
    let semantic_id = content_id::semantic_id(
        crate::compiler_semantics_id(),
        &linked_ir_json,
        &closure_json,
    );

    // Every used external Lean entry, for the probe module (§18.8).
    let mut external_used: BTreeMap<String, ExternalConstRef> = BTreeMap::new();
    for module in modules.values() {
        collect_document_externals(&module.document, &mut external_used);
    }

    Ok(CheckedProject {
        modules,
        linked,
        closure,
        visible_union,
        external_used,
        source_id,
        semantic_id,
        canonical_lock,
    })
}

fn topo_order(loaded: &BTreeMap<String, ModuleLoad>) -> Result<Vec<String>, String> {
    let mut order = Vec::new();
    let mut state: BTreeMap<&str, u8> = BTreeMap::new();
    fn visit<'a>(
        name: &'a str,
        loaded: &'a BTreeMap<String, ModuleLoad>,
        state: &mut BTreeMap<&'a str, u8>,
        order: &mut Vec<String>,
    ) -> Result<(), String> {
        match state.get(name) {
            Some(1) => return Err(name.to_owned()),
            Some(2) => return Ok(()),
            _ => {}
        }
        state.insert(name, 1);
        if let Some(load) = loaded.get(name) {
            for import in &load.ast.imports {
                if loaded.contains_key(&import.text) {
                    let key = loaded
                        .get_key_value(&import.text)
                        .map(|(k, _)| k.as_str())
                        .unwrap_or(name);
                    visit(key, loaded, state, order)?;
                }
            }
        }
        state.insert(name, 2);
        order.push(name.to_owned());
        Ok(())
    }
    let keys: Vec<&str> = loaded.keys().map(String::as_str).collect();
    for name in keys {
        visit(name, loaded, &mut state, &mut order)?;
    }
    Ok(order)
}

fn elab_phrase(
    shared: &Shared<'_>,
    scopes: &mut ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    range: AtomRange,
) -> Result<(Phrase, Vec<SourceRow>), Diagnostic> {
    let tokens = text_tokens(shared.path, shared.atoms, range.0, range.1)?;
    let parser = TextParser {
        path: shared.path,
        atoms: shared.atoms,
        tokens: &tokens,
        closure: shared.closure,
        visible: shared.visible,
    };
    let items = parse_phrase(&parser, budget)?;
    let mut rows = Vec::new();
    let mut phrase = Phrase::default();
    for item in items {
        match item {
            PhraseItemAst::Word { candidates, atoms } => {
                let mut entries: Vec<&crate::lexicon::resolve::FormRef> =
                    candidates.iter().collect();
                entries.dedup_by(|a, b| a.package == b.package && a.entry == b.entry);
                if entries.len() != 1 {
                    let first = &shared.atoms[atoms.0];
                    return Err(Diagnostic::new(
                        code!("LLP2002"),
                        "more than one distinct concept interpretation survives in a phrase",
                    )
                    .with_span(first.span(shared.path)));
                }
                let reference = entries[0];
                let (byte_start, byte_end) = bytes_of(shared.atoms, atoms);
                rows.push(SourceRow {
                    path: shared.path.to_owned(),
                    byte_start,
                    byte_end,
                    class: AtomClass::Word,
                    binding: Origin::Form {
                        package: reference.package.clone(),
                        entry: reference.entry.clone(),
                        form: reference.form.clone(),
                    },
                });
                phrase.items.push(PhraseItem::Word {
                    entry: QualifiedId {
                        package: reference.package.clone(),
                        entry: reference.entry.clone(),
                    },
                    form: reference.form.clone(),
                });
            }
            PhraseItemAst::Math(island) => {
                let result = elab_island(shared, scopes, alloc, budget, &island, None)?;
                if matches!(&result.ty, Some(ty) if crate::ir::term::is_prop(ty)) {
                    let first = &shared.atoms[island.first_atom()];
                    return Err(Diagnostic::new(
                        code!("LLP2003"),
                        "a phrase cannot contain a proposition",
                    )
                    .with_span(first.span(shared.path)));
                }
                rows.extend(result.rows);
                phrase.items.push(PhraseItem::Math(result.term));
            }
            PhraseItemAst::Punctuation { atom, entry } => {
                let a = &shared.atoms[atom];
                rows.push(SourceRow {
                    path: shared.path.to_owned(),
                    byte_start: a.byte_start,
                    byte_end: a.byte_end,
                    class: a.class,
                    binding: Origin::Structural {
                        package: "lexlean.core".to_owned(),
                        entry: entry.to_owned(),
                    },
                });
                phrase.items.push(PhraseItem::Punctuation(QualifiedId {
                    package: "lexlean.core".to_owned(),
                    entry: entry.to_owned(),
                }));
            }
        }
    }
    Ok((phrase, rows))
}

/// Parse and elaborate a `\parameters{...}` binder list (§15.4).
fn elab_binder_list(
    shared: &Shared<'_>,
    scopes: &mut ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    range: AtomRange,
    rows: &mut Vec<SourceRow>,
) -> Result<Vec<Binder>, Diagnostic> {
    let tokens = text_tokens(shared.path, shared.atoms, range.0, range.1)?;
    let parser = TextParser {
        path: shared.path,
        atoms: shared.atoms,
        tokens: &tokens,
        closure: shared.closure,
        visible: shared.visible,
    };
    let mut binders = Vec::new();
    let mut pos = 0usize;
    loop {
        let alternatives = parser.binder(pos, budget, false)?;
        // A parameter binder must end at `;` or the end of the list; a
        // surviving split is ambiguity (I5).
        let valid: Vec<(usize, crate::grammar::proposition::BinderAst)> = alternatives
            .into_iter()
            .filter(|(end, _)| {
                *end == tokens.len()
                    || matches!(
                        tokens.get(*end),
                        Some(TextToken::Atom(index))
                            if shared.atoms[*index].text == ";"
                    )
            })
            .collect();
        match valid.len() {
            1 => {}
            0 => {
                return Err(Diagnostic::new(
                    code!("LLP2001"),
                    "no parse for a parameter binder",
                ));
            }
            _ => {
                return Err(Diagnostic::new(
                    code!("LLP2002"),
                    "ambiguous parameter binder",
                ));
            }
        }
        let (end, ast) = valid.into_iter().next().expect("one");
        let (binder, binder_rows) = elab_binder(shared, scopes, alloc, budget, &ast)?;
        rows.extend(binder_rows);
        binders.push(binder);
        if end == tokens.len() {
            break;
        }
        if let Some(TextToken::Atom(index)) = tokens.get(end) {
            let atom = &shared.atoms[*index];
            rows.push(SourceRow {
                path: shared.path.to_owned(),
                byte_start: atom.byte_start,
                byte_end: atom.byte_end,
                class: atom.class,
                binding: Origin::Structural {
                    package: "lexlean.core".to_owned(),
                    entry: "semicolon".to_owned(),
                },
            });
        }
        pos = end + 1;
    }
    Ok(binders)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn link_block(
    project: &Project,
    closure: &Closure,
    visible: &BTreeSet<String>,
    module_decls: &mut DeclTable,
    global_decls: &mut DeclTable,
    module_name: &str,
    lean_module: &str,
    load: &ModuleLoad,
    scopes: &mut ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    rows: &mut Vec<SourceRow>,
    components: &mut BTreeSet<String>,
    lean_names: &mut BTreeSet<String>,
    decl_origins: &mut BTreeMap<String, DeclOrigin>,
    proof_spellings: &mut BTreeMap<LocalId, String>,
    block: &BlockAst,
) -> Result<Block, Diagnostic> {
    match block {
        BlockAst::Section {
            component,
            heading,
            params,
            blocks,
            begin: _,
        } => {
            if !components.insert(component.text.clone()) {
                return Err(Diagnostic::new(
                    code!("LLP2003"),
                    format!("component `{}` is declared twice", component.text),
                ));
            }
            let shared = Shared {
                path: &load.path,
                atoms: &load.atoms,
                closure,
                visible,
                decls: module_decls,
                module: module_name,
                module_prefix: &project.config.module_prefix,
            };
            let (heading_phrase, heading_rows) =
                elab_phrase(&shared, scopes, alloc, budget, *heading)?;
            rows.extend(heading_rows);
            scopes.push_frame();
            let section_params = match params {
                Some(range) => {
                    match elab_binder_list(&shared, scopes, alloc, budget, *range, rows) {
                        Ok(binders) => binders,
                        Err(diagnostic) => {
                            scopes.pop_frame();
                            return Err(diagnostic);
                        }
                    }
                }
                None => Vec::new(),
            };
            let mut inner = Vec::new();
            for child in blocks {
                match link_block(
                    project,
                    closure,
                    visible,
                    module_decls,
                    global_decls,
                    module_name,
                    lean_module,
                    load,
                    scopes,
                    alloc,
                    budget,
                    rows,
                    components,
                    lean_names,
                    decl_origins,
                    proof_spellings,
                    child,
                ) {
                    Ok(linked) => inner.push(linked),
                    Err(diagnostic) => {
                        scopes.pop_frame();
                        return Err(diagnostic);
                    }
                }
            }
            scopes.pop_frame();
            Ok(Block::Section(Section {
                component: component.text.clone(),
                heading: heading_phrase,
                params: section_params,
                blocks: inner,
            }))
        }
        BlockAst::Declaration(decl) => {
            let declaration = link_declaration(
                project,
                closure,
                visible,
                module_decls,
                global_decls,
                module_name,
                lean_module,
                load,
                scopes,
                alloc,
                budget,
                rows,
                components,
                lean_names,
                decl_origins,
                proof_spellings,
                decl,
            )?;
            Ok(Block::Declaration(Box::new(declaration)))
        }
    }
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn link_declaration(
    project: &Project,
    closure: &Closure,
    visible: &BTreeSet<String>,
    module_decls: &mut DeclTable,
    global_decls: &mut DeclTable,
    module_name: &str,
    lean_module: &str,
    load: &ModuleLoad,
    scopes: &mut ScopeStack,
    alloc: &mut LocalAlloc,
    budget: &mut Budget,
    rows: &mut Vec<SourceRow>,
    components: &mut BTreeSet<String>,
    lean_names: &mut BTreeSet<String>,
    decl_origins: &mut BTreeMap<String, DeclOrigin>,
    proof_spellings: &mut BTreeMap<LocalId, String>,
    decl: &DeclAst,
) -> Result<Declaration, Diagnostic> {
    if !components.insert(decl.component.text.clone()) {
        return Err(Diagnostic::new(
            code!("LLP2003"),
            format!("component `{}` is declared twice", decl.component.text),
        ));
    }
    // Name generation (§17.8): `-` to `_`, collision and keyword checked.
    let lean_name = decl.component.text.replace('-', "_");
    if LEAN_KEYWORDS.contains(&lean_name.as_str()) || !lean_names.insert(lean_name.clone()) {
        return Err(Diagnostic::new(
            code!("LLP2003"),
            format!("generated Lean name `{lean_name}` collides"),
        ));
    }
    let policy = match decl.policy.kind {
        PolicyKind::None => AxiomPolicy::None,
        PolicyKind::Allow => AxiomPolicy::Allow(decl.policy.names.clone()),
        PolicyKind::Exact => AxiomPolicy::Exact(decl.policy.names.clone()),
    };
    let shared = Shared {
        path: &load.path,
        atoms: &load.atoms,
        closure,
        visible,
        decls: module_decls,
        module: module_name,
        module_prefix: &project.config.module_prefix,
    };
    let origin = DeclOrigin {
        whole: bytes_of(&load.atoms, (decl.begin, decl.end)),
        sentence: bytes_of(
            &load.atoms,
            (decl.sentence.range.0, decl.sentence.period + 1),
        ),
        proof: decl
            .proof
            .as_ref()
            .map(|proof| bytes_of(&load.atoms, (proof.begin, decl.end))),
    };
    decl_origins.insert(decl.component.text.clone(), origin);

    let (body, _decl_ty) = if decl.kind.is_theorem_like() {
        // The proposition sentence (§15.6, §15.8).
        let tokens = text_tokens(
            &load.path,
            &load.atoms,
            decl.sentence.range.0,
            decl.sentence.range.1,
        )?;
        let parser = TextParser {
            path: &load.path,
            atoms: &load.atoms,
            tokens: &tokens,
            closure,
            visible,
        };
        let alternatives = parser.proposition_sentence(budget)?;
        let (statement, statement_rows) =
            elab_proposition_sentence(&shared, scopes, alloc, budget, &alternatives)?;
        rows.extend(statement_rows);
        let period = &load.atoms[decl.sentence.period];
        rows.push(SourceRow {
            path: load.path.clone(),
            byte_start: period.byte_start,
            byte_end: period.byte_end,
            class: period.class,
            binding: Origin::Structural {
                package: "lexlean.core".to_owned(),
                entry: "period".to_owned(),
            },
        });

        // Leading named universal binders are in scope when the proof
        // begins (§18.5); anonymous implication binders are not.
        let proof_ast = decl.proof.as_ref().ok_or_else(|| {
            Diagnostic::new(
                code!("LLF5005"),
                "a theorem-like declaration without a proof is not valid",
            )
        })?;
        scopes.push_frame();
        let mut goal = statement.clone();
        loop {
            match goal {
                Term::Pi { ref binders, .. }
                    if binders.iter().all(|binder| !binder.spelling.is_empty()) =>
                {
                    let Term::Pi { binders, body } = goal else {
                        unreachable!("matched above");
                    };
                    for binder in &binders {
                        scopes.declare(&binder.spelling, binder.id, Some(binder.ty.clone()));
                    }
                    goal = *body;
                }
                _ => break,
            }
        }
        let mut proof_elab = ProofElab {
            shared: &shared,
            scopes,
            alloc,
            budget,
            rows: Vec::new(),
            spellings: BTreeMap::new(),
        };
        let proof_result = proof_elab.elab_env(proof_ast, Some(goal));
        let proof_rows = std::mem::take(&mut proof_elab.rows);
        let step_spellings = std::mem::take(&mut proof_elab.spellings);
        scopes.pop_frame();
        rows.extend(proof_rows);
        proof_spellings.extend(step_spellings);
        let proof = proof_result?;
        (
            DeclBody::TheoremLike {
                statement: statement.clone(),
                proof,
            },
            statement,
        )
    } else {
        let definition = elab_definition(&shared, scopes, alloc, budget, decl, &decl.sentence)?;
        rows.extend(definition.rows.clone());
        (
            DeclBody::Definition {
                entry: definition.entry,
                ty: definition.ty.clone(),
                value: definition.value,
            },
            definition.ty,
        )
    };

    // Inherited section parameters actually used (§17.5, §18.3).
    let mut used: BTreeSet<LocalId> = BTreeSet::new();
    match &body {
        DeclBody::TheoremLike { statement, proof } => {
            collect_term_locals(statement, &mut used);
            collect_proof_locals(proof, &mut used);
        }
        DeclBody::Definition { ty, value, .. } => {
            collect_term_locals(ty, &mut used);
            collect_term_locals(value, &mut used);
        }
    }
    let params: Vec<Binder> = scopes
        .entries()
        .into_iter()
        .filter(|entry| used.contains(&entry.id))
        .map(|entry| Binder {
            id: entry.id,
            mode: crate::lexicon::lse::BinderMode::Explicit,
            ty: entry.ty.clone().unwrap_or_else(crate::ir::term::prop),
            spelling: entry.spelling.clone(),
        })
        .collect();

    let full_lean_name = format!("{lean_module}.{lean_name}");
    let info_ty = match &body {
        DeclBody::TheoremLike { statement, .. } => statement.clone(),
        DeclBody::Definition { ty, .. } => ty.clone(),
    };
    let info = DeclInfo {
        module: module_name.to_owned(),
        component: decl.component.text.clone(),
        lean_name: full_lean_name,
        ty: info_ty,
    };
    module_decls.rows.push(info.clone());
    global_decls.rows.push(info);

    Ok(Declaration {
        component: decl.component.text.clone(),
        lean_name,
        kind: decl.kind,
        params,
        body,
        policy,
    })
}

fn collect_term_locals(term: &Term, out: &mut BTreeSet<LocalId>) {
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
            collect_term_locals(function, out);
            for argument in explicit_args {
                collect_term_locals(argument, out);
            }
        }
        Term::Pi { binders, body } | Term::Lambda { binders, body } => {
            for binder in binders {
                collect_term_locals(&binder.ty, out);
            }
            collect_term_locals(body, out);
        }
        Term::Let {
            binder,
            value,
            body,
        } => {
            collect_term_locals(&binder.ty, out);
            collect_term_locals(value, out);
            collect_term_locals(body, out);
        }
        Term::NatLiteral { expected_type, .. } => collect_term_locals(expected_type, out),
    }
}

fn collect_proof_locals(proof: &Proof, out: &mut BTreeSet<LocalId>) {
    match proof {
        Proof::Sequence(steps) => {
            for step in steps {
                collect_proof_locals(step, out);
            }
        }
        Proof::Intro(_) | Proof::Reflexivity | Proof::SelectLeft | Proof::SelectRight => {}
        Proof::Exact(term) | Proof::ApplyOne(term) | Proof::Witness(term) => {
            collect_term_locals(term, out);
        }
        Proof::Apply { function, premises } => {
            collect_term_locals(function, out);
            for premise in premises {
                collect_proof_locals(premise, out);
            }
        }
        Proof::Have {
            proposition, proof, ..
        } => {
            collect_term_locals(proposition, out);
            collect_proof_locals(proof, out);
        }
        Proof::Rewrite { rules, .. } => {
            for rule in rules {
                collect_term_locals(&rule.term, out);
            }
        }
        Proof::SimplifyOnly { rules, .. } => {
            for rule in rules {
                collect_term_locals(rule, out);
            }
        }
        Proof::Constructor(branches) => {
            for branch in branches {
                collect_proof_locals(branch, out);
            }
        }
        Proof::Cases { scrutinee, cases } | Proof::Induction { scrutinee, cases } => {
            collect_term_locals(scrutinee, out);
            for case in cases {
                collect_proof_locals(&case.proof, out);
            }
        }
        Proof::Calculate { start, steps, .. } => {
            collect_term_locals(start, out);
            for step in steps {
                collect_term_locals(&step.term, out);
                collect_term_locals(&step.proof, out);
            }
        }
    }
}

fn count_ir_nodes(document: &DocumentModule) -> u64 {
    // A coarse, deterministic node count for the explicit resource policy.
    fn term_nodes(term: &Term) -> u64 {
        1 + match term {
            Term::App {
                function,
                explicit_args,
                ..
            } => term_nodes(function) + explicit_args.iter().map(term_nodes).sum::<u64>(),
            Term::Pi { binders, body } | Term::Lambda { binders, body } => {
                binders
                    .iter()
                    .map(|binder| term_nodes(&binder.ty))
                    .sum::<u64>()
                    + term_nodes(body)
            }
            Term::Let {
                binder,
                value,
                body,
            } => term_nodes(&binder.ty) + term_nodes(value) + term_nodes(body),
            Term::NatLiteral { expected_type, .. } => term_nodes(expected_type),
            _ => 0,
        }
    }
    fn proof_nodes(proof: &Proof) -> u64 {
        1 + match proof {
            Proof::Sequence(steps) => steps.iter().map(proof_nodes).sum::<u64>(),
            Proof::Exact(term) | Proof::ApplyOne(term) | Proof::Witness(term) => term_nodes(term),
            Proof::Apply { function, premises } => {
                term_nodes(function) + premises.iter().map(proof_nodes).sum::<u64>()
            }
            Proof::Have {
                proposition, proof, ..
            } => term_nodes(proposition) + proof_nodes(proof),
            Proof::Rewrite { rules, .. } => rules.iter().map(|rule| term_nodes(&rule.term)).sum(),
            Proof::SimplifyOnly { rules, .. } => rules.iter().map(term_nodes).sum(),
            Proof::Constructor(branches) => branches.iter().map(proof_nodes).sum(),
            Proof::Cases { scrutinee, cases } | Proof::Induction { scrutinee, cases } => {
                term_nodes(scrutinee)
                    + cases
                        .iter()
                        .map(|case: &CaseProof| proof_nodes(&case.proof))
                        .sum::<u64>()
            }
            Proof::Calculate { start, steps, .. } => {
                term_nodes(start)
                    + steps
                        .iter()
                        .map(|step| term_nodes(&step.term) + term_nodes(&step.proof))
                        .sum::<u64>()
            }
            _ => 0,
        }
    }
    fn block_nodes(block: &Block) -> u64 {
        match block {
            Block::Section(section) => {
                1 + section.blocks.iter().map(block_nodes).sum::<u64>()
                    + section
                        .params
                        .iter()
                        .map(|binder| term_nodes(&binder.ty))
                        .sum::<u64>()
            }
            Block::Declaration(declaration) => {
                1 + match &declaration.body {
                    DeclBody::TheoremLike { statement, proof } => {
                        term_nodes(statement) + proof_nodes(proof)
                    }
                    DeclBody::Definition { ty, value, .. } => term_nodes(ty) + term_nodes(value),
                }
            }
        }
    }
    document.blocks.iter().map(block_nodes).sum()
}

/// Collect every external Lean entry a document references, keyed by
/// qualified entry ID (§18.8, §18.3).
pub fn collect_document_externals(
    document: &DocumentModule,
    out: &mut BTreeMap<String, ExternalConstRef>,
) {
    fn term_externals(term: &Term, out: &mut BTreeMap<String, ExternalConstRef>) {
        match term {
            Term::Global(GlobalRef::External(external), _) => {
                out.insert(external.entry.clone(), external.clone());
            }
            Term::Global(..) | Term::Local(_) | Term::Sort(_) => {}
            Term::App {
                function,
                explicit_args,
                ..
            } => {
                term_externals(function, out);
                for argument in explicit_args {
                    term_externals(argument, out);
                }
            }
            Term::Pi { binders, body } | Term::Lambda { binders, body } => {
                for binder in binders {
                    term_externals(&binder.ty, out);
                }
                term_externals(body, out);
            }
            Term::Let {
                binder,
                value,
                body,
            } => {
                term_externals(&binder.ty, out);
                term_externals(value, out);
                term_externals(body, out);
            }
            Term::NatLiteral { expected_type, .. } => term_externals(expected_type, out),
        }
    }
    fn proof_externals(proof: &Proof, out: &mut BTreeMap<String, ExternalConstRef>) {
        match proof {
            Proof::Sequence(steps) => steps.iter().for_each(|step| proof_externals(step, out)),
            Proof::Exact(term) | Proof::ApplyOne(term) | Proof::Witness(term) => {
                term_externals(term, out);
            }
            Proof::Apply { function, premises } => {
                term_externals(function, out);
                premises
                    .iter()
                    .for_each(|premise| proof_externals(premise, out));
            }
            Proof::Have {
                proposition, proof, ..
            } => {
                term_externals(proposition, out);
                proof_externals(proof, out);
            }
            Proof::Rewrite { rules, .. } => rules
                .iter()
                .for_each(|rule| term_externals(&rule.term, out)),
            Proof::SimplifyOnly { rules, .. } => {
                rules.iter().for_each(|rule| term_externals(rule, out));
            }
            Proof::Constructor(branches) => branches
                .iter()
                .for_each(|branch| proof_externals(branch, out)),
            Proof::Cases { scrutinee, cases } | Proof::Induction { scrutinee, cases } => {
                term_externals(scrutinee, out);
                cases
                    .iter()
                    .for_each(|case| proof_externals(&case.proof, out));
            }
            Proof::Calculate { start, steps, .. } => {
                term_externals(start, out);
                for step in steps {
                    term_externals(&step.term, out);
                    term_externals(&step.proof, out);
                }
            }
            _ => {}
        }
    }
    fn walk_blocks(blocks: &[Block], out: &mut BTreeMap<String, ExternalConstRef>) {
        for block in blocks {
            match block {
                Block::Section(section) => {
                    for binder in &section.params {
                        term_externals(&binder.ty, out);
                    }
                    for item in &section.heading.items {
                        if let PhraseItem::Math(term) = item {
                            term_externals(term, out);
                        }
                    }
                    walk_blocks(&section.blocks, out);
                }
                Block::Declaration(declaration) => {
                    for binder in &declaration.params {
                        term_externals(&binder.ty, out);
                    }
                    match &declaration.body {
                        DeclBody::TheoremLike { statement, proof } => {
                            term_externals(statement, out);
                            proof_externals(proof, out);
                        }
                        DeclBody::Definition { ty, value, .. } => {
                            term_externals(ty, out);
                            term_externals(value, out);
                        }
                    }
                }
            }
        }
    }
    for item in &document.title.items {
        if let PhraseItem::Math(term) = item {
            term_externals(term, out);
        }
    }
    walk_blocks(&document.blocks, out);
}

/// Every external and defined entry a term set references; used by backends
/// through the checked project.
pub fn signature_term_of(
    shared: &Shared<'_>,
    alloc: &mut LocalAlloc,
    entry: &crate::lexicon::entry::Entry,
) -> Result<Term, String> {
    let signature = entry
        .signature
        .as_ref()
        .ok_or_else(|| "entry has no signature".to_owned())?;
    lse_to_term(signature, shared, alloc, &BTreeMap::new())
}
