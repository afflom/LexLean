//! The linked glossary closure: cross-package validation and the surface
//! index the token lattice matches against (SPEC.md §13.11, §14.1).

use std::collections::{BTreeMap, BTreeSet};

use crate::artifact::canonical_json::Json;
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::lexicon::entry::{Category, Channel, Denotation, Entry};
use crate::lexicon::lse::QualifiedId;
use crate::lexicon::package::LexiconPackage;
use crate::lexicon::{Bootstrap, TokenRegistry};
use crate::source::atom::{Atom, AtomClass};

/// A reference to one form of one entry.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FormRef {
    /// The package ID.
    pub package: String,
    /// The local entry ID.
    pub entry: String,
    /// The form ID.
    pub form: String,
}

/// The loaded glossary closure for a project.
#[derive(Debug)]
pub struct Closure {
    /// Packages in dependency order, `lexlean.core` first.
    pub packages: Vec<LexiconPackage>,
    /// The renderer-token registry.
    pub registry: TokenRegistry,
    /// The bootstrap data.
    pub bootstrap: Bootstrap,
    package_index: BTreeMap<String, usize>,
    surface_index: BTreeMap<(AtomClass, String), Vec<FormRef>>,
}

impl Closure {
    /// Build and cross-validate the closure (§13.11). `packages` arrive in
    /// any order; the closure orders them by dependency with core first.
    #[allow(clippy::too_many_lines)]
    pub fn build(
        packages: Vec<LexiconPackage>,
        registry: TokenRegistry,
        bootstrap: Bootstrap,
        max_import_depth: u64,
    ) -> Result<Self, Vec<Diagnostic>> {
        let mut diagnostics: Vec<Diagnostic> = Vec::new();

        // Unique package IDs (LLR3002).
        let mut by_id: BTreeMap<String, usize> = BTreeMap::new();
        for (index, package) in packages.iter().enumerate() {
            if by_id.insert(package.id.clone(), index).is_some() {
                diagnostics.push(Diagnostic::new(
                    code!("LLR3002"),
                    format!("duplicate package `{}`", package.id),
                ));
            }
        }
        if !diagnostics.is_empty() {
            return Err(diagnostics);
        }

        // Imports exist with the exact version (LLR3001), the graph is
        // acyclic (LLR3003), and depth stays within the explicit limit
        // (LLS8002).
        for package in &packages {
            for import in &package.imports {
                match by_id.get(&import.package) {
                    Some(&target) if packages[target].version == import.version => {}
                    Some(_) => diagnostics.push(Diagnostic::new(
                        code!("LLR3001"),
                        format!(
                            "{}: import `{import}` does not match the loaded version",
                            package.id
                        ),
                    )),
                    None => diagnostics.push(Diagnostic::new(
                        code!("LLR3001"),
                        format!("{}: import `{import}` is not available", package.id),
                    )),
                }
            }
        }
        if !diagnostics.is_empty() {
            return Err(diagnostics);
        }

        // Topological order with cycle detection and longest-chain depth.
        let mut order: Vec<usize> = Vec::new();
        let mut state: Vec<u8> = vec![0; packages.len()]; // 0 new, 1 open, 2 done
        let mut depth: Vec<u64> = vec![0; packages.len()];
        fn visit(
            node: usize,
            packages: &[LexiconPackage],
            by_id: &BTreeMap<String, usize>,
            state: &mut [u8],
            depth: &mut [u64],
            order: &mut Vec<usize>,
        ) -> Result<u64, String> {
            match state[node] {
                1 => return Err(packages[node].id.clone()),
                2 => return Ok(depth[node]),
                _ => {}
            }
            state[node] = 1;
            let mut deepest = 0u64;
            for import in &packages[node].imports {
                let target = by_id[&import.package];
                let below = visit(target, packages, by_id, state, depth, order)?;
                deepest = deepest.max(below.saturating_add(1));
            }
            state[node] = 2;
            depth[node] = deepest;
            order.push(node);
            Ok(deepest)
        }
        for index in 0..packages.len() {
            match visit(index, &packages, &by_id, &mut state, &mut depth, &mut order) {
                Ok(package_depth) => {
                    if package_depth >= max_import_depth {
                        diagnostics.push(Diagnostic::new(
                            code!("LLS8002"),
                            format!(
                                "max_import_depth exceeded: configured {max_import_depth}, package {}",
                                packages[index].id
                            ),
                        ));
                    }
                }
                Err(cycle_member) => {
                    diagnostics.push(Diagnostic::new(
                        code!("LLR3003"),
                        format!("package import cycle through `{cycle_member}`"),
                    ));
                    return Err(diagnostics);
                }
            }
        }
        // Reorder by topological position, core first.
        let ordered: Vec<LexiconPackage> = {
            let mut slots: Vec<Option<LexiconPackage>> = packages.into_iter().map(Some).collect();
            order
                .iter()
                .map(|&index| slots[index].take().expect("each node visited once"))
                .collect()
        };
        let package_index: BTreeMap<String, usize> = ordered
            .iter()
            .enumerate()
            .map(|(index, package)| (package.id.clone(), index))
            .collect();

        let lookup = |id: &QualifiedId| -> Option<&Entry> {
            package_index
                .get(&id.package)
                .and_then(|&index| ordered[index].entries.get(&id.entry))
        };

        // Cross-entry validation.
        for package in &ordered {
            for entry in package.entries.values() {
                let where_ = format!("{}::{}", package.id, entry.id);
                if let Some(signature) = &entry.signature {
                    for reference in signature.referenced_consts() {
                        if lookup(&reference).is_none() {
                            diagnostics.push(Diagnostic::new(
                                code!("LLR3005"),
                                format!("{where_}: signature references unresolved `{reference}`"),
                            ));
                        }
                    }
                }
                if let Denotation::Defined { value, .. } = &entry.denotation {
                    for reference in value.referenced_consts() {
                        if lookup(&reference).is_none() {
                            diagnostics.push(Diagnostic::new(
                                code!("LLR3005"),
                                format!(
                                    "{where_}: defined value references unresolved `{reference}`"
                                ),
                            ));
                        }
                    }
                }
                for render in [&entry.render_math, &entry.render_text]
                    .into_iter()
                    .flatten()
                {
                    for token in render.tokens() {
                        match registry.get(&token) {
                            Some(row) => {
                                if row.channel == "text"
                                    && entry.render_math.as_ref() == Some(render)
                                {
                                    // Structure-only tokens never appear in a
                                    // math template.
                                    diagnostics.push(Diagnostic::new(
                                        code!("LLR3004"),
                                        format!("{where_}: token `{token}` is not a math token"),
                                    ));
                                }
                            }
                            None => diagnostics.push(Diagnostic::new(
                                code!("LLR3004"),
                                format!("{where_}: unknown renderer token `{token}`"),
                            )),
                        }
                    }
                    for (entry_ref, form_id) in render.form_refs() {
                        match lookup(&entry_ref) {
                            Some(target) if target.forms.iter().any(|f| f.id == form_id) => {}
                            Some(_) => diagnostics.push(Diagnostic::new(
                                code!("LLR3004"),
                                format!("{where_}: render references unknown form `{entry_ref}`/`{form_id}`"),
                            )),
                            None => diagnostics.push(Diagnostic::new(
                                code!("LLR3004"),
                                format!("{where_}: render references unresolved `{entry_ref}`"),
                            )),
                        }
                    }
                }
                if let Some(eliminator) = &entry.eliminator {
                    for constructor in &eliminator.constructors {
                        if lookup(&constructor.entry).is_none() {
                            diagnostics.push(Diagnostic::new(
                                code!("LLR3004"),
                                format!(
                                    "{where_}: eliminator references absent constructor `{}`",
                                    constructor.entry
                                ),
                            ));
                        }
                    }
                }
            }
        }

        // Defined-denotation acyclicity (§13.6, LLR3003).
        {
            let defined: Vec<(QualifiedId, Vec<QualifiedId>)> = ordered
                .iter()
                .flat_map(|package| {
                    package.entries.values().filter_map(move |entry| {
                        if let Denotation::Defined { value, .. } = &entry.denotation {
                            Some((
                                QualifiedId {
                                    package: package.id.clone(),
                                    entry: entry.id.clone(),
                                },
                                value.referenced_consts(),
                            ))
                        } else {
                            None
                        }
                    })
                })
                .collect();
            let ids: BTreeSet<String> = defined.iter().map(|(id, _)| id.to_string()).collect();
            let edges: BTreeMap<String, Vec<String>> = defined
                .iter()
                .map(|(id, references)| {
                    (
                        id.to_string(),
                        references
                            .iter()
                            .map(ToString::to_string)
                            .filter(|reference| ids.contains(reference))
                            .collect(),
                    )
                })
                .collect();
            let mut mark: BTreeMap<String, u8> = BTreeMap::new();
            fn cyclic(
                node: &str,
                edges: &BTreeMap<String, Vec<String>>,
                mark: &mut BTreeMap<String, u8>,
            ) -> bool {
                match mark.get(node) {
                    Some(1) => return true,
                    Some(2) => return false,
                    _ => {}
                }
                mark.insert(node.to_owned(), 1);
                if let Some(next) = edges.get(node) {
                    for target in next {
                        if cyclic(target, edges, mark) {
                            return true;
                        }
                    }
                }
                mark.insert(node.to_owned(), 2);
                false
            }
            for id in edges.keys() {
                if cyclic(id, &edges, &mut mark) {
                    diagnostics.push(Diagnostic::new(
                        code!("LLR3003"),
                        format!("defined-denotation cycle through `{id}`"),
                    ));
                    break;
                }
            }
        }

        if !diagnostics.is_empty() {
            return Err(diagnostics);
        }

        // The surface index: every form keyed by its first non-whitespace
        // atom. Import order gives no priority (§14.1): candidates are kept
        // in deterministic package/entry/form order.
        let mut surface_index: BTreeMap<(AtomClass, String), Vec<FormRef>> = BTreeMap::new();
        for package in &ordered {
            for entry in package.entries.values() {
                for form in &entry.forms {
                    let Some(first) = form
                        .atoms
                        .iter()
                        .find(|atom| atom.class != AtomClass::Whitespace)
                    else {
                        continue;
                    };
                    surface_index
                        .entry((first.class, first.text.clone()))
                        .or_default()
                        .push(FormRef {
                            package: package.id.clone(),
                            entry: entry.id.clone(),
                            form: form.id.clone(),
                        });
                }
            }
        }

        Ok(Self {
            packages: ordered,
            registry,
            bootstrap,
            package_index,
            surface_index,
        })
    }

    /// Look up an entry by qualified ID.
    #[must_use]
    pub fn entry(&self, id: &QualifiedId) -> Option<&Entry> {
        self.package_index
            .get(&id.package)
            .and_then(|&index| self.packages[index].entries.get(&id.entry))
    }

    /// Look up a package.
    #[must_use]
    pub fn package(&self, id: &str) -> Option<&LexiconPackage> {
        self.package_index
            .get(id)
            .map(|&index| &self.packages[index])
    }

    /// The form of a [`FormRef`].
    #[must_use]
    pub fn form(&self, reference: &FormRef) -> Option<(&Entry, &crate::lexicon::entry::Form)> {
        let entry = self.entry(&QualifiedId {
            package: reference.package.clone(),
            entry: reference.entry.clone(),
        })?;
        let form = entry.forms.iter().find(|form| form.id == reference.form)?;
        Some((entry, form))
    }

    /// All form matches starting at atom `start` (§14.1): every glossary
    /// form whose primitive-atom sequence begins there, restricted to
    /// `channel` and the `visible` package set. Returns `(form, end)` with
    /// `end` the exclusive atom index. Multiword separators match exactly
    /// one whitespace atom. A match never ends inside a composed identifier.
    #[must_use]
    pub fn matches_at(
        &self,
        atoms: &[Atom],
        start: usize,
        channel: Channel,
        visible: &BTreeSet<String>,
    ) -> Vec<(FormRef, usize)> {
        let Some(first) = atoms.get(start) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        let Some(candidates) = self.surface_index.get(&(first.class, first.text.clone())) else {
            return Vec::new();
        };
        'candidate: for reference in candidates {
            if !visible.contains(&reference.package) {
                continue;
            }
            let Some((_, form)) = self.form(reference) else {
                continue;
            };
            if !form.channel.covers(channel) {
                continue;
            }
            let mut source_at = start;
            for form_atom in &form.atoms {
                if form_atom.class == AtomClass::Whitespace {
                    match atoms.get(source_at) {
                        Some(atom) if atom.class == AtomClass::Whitespace => source_at += 1,
                        _ => continue 'candidate,
                    }
                    continue;
                }
                match atoms.get(source_at) {
                    Some(atom) if atom.class == form_atom.class && atom.text == form_atom.text => {
                        source_at += 1;
                    }
                    _ => continue 'candidate,
                }
            }
            // Do not end inside a composed identifier (§12.2 class 3): a
            // word- or numeral-final match followed byte-adjacently by more
            // identifier material is not this form.
            if let (Some(last), Some(next)) = (atoms.get(source_at - 1), atoms.get(source_at)) {
                let last_is_ident = matches!(last.class, AtomClass::Word | AtomClass::Numeral);
                let next_extends = next.byte_start == last.byte_end
                    && match next.class {
                        AtomClass::Word | AtomClass::Numeral => true,
                        AtomClass::AsciiSymbol => next.text == "_" || next.text == "'",
                        _ => false,
                    };
                if last_is_ident && next_extends {
                    continue;
                }
            }
            out.push((reference.clone(), source_at));
        }
        out
    }

    /// The set of packages visible to a module: the used packages plus their
    /// transitive imports plus `lexlean.core`.
    #[must_use]
    pub fn visible_set(&self, used: &[String]) -> BTreeSet<String> {
        let mut visible: BTreeSet<String> = BTreeSet::new();
        let mut stack: Vec<String> = used.to_vec();
        stack.push("lexlean.core".to_owned());
        while let Some(id) = stack.pop() {
            if !visible.insert(id.clone()) {
                continue;
            }
            if let Some(package) = self.package(&id) {
                for import in &package.imports {
                    stack.push(import.package.clone());
                }
            }
        }
        visible
    }

    /// The canonical linked-lexicon JSON for the semantic ID (§21.4) and the
    /// per-module closure artifact, over the packages in `visible`.
    #[must_use]
    pub fn closure_json(&self, module: &str, visible: &BTreeSet<String>) -> Json {
        let packages = self
            .packages
            .iter()
            .filter(|package| visible.contains(&package.id))
            .map(|package| {
                let entries = package
                    .entries
                    .values()
                    .map(|entry| {
                        let mut fields = vec![
                            ("id", Json::Str(entry.id.clone())),
                            ("category", Json::Str(entry.category.as_str().to_owned())),
                        ];
                        if let Some(hash) = &entry.signature_hash {
                            fields.push(("signature_sha256", Json::Str(hash.to_hex())));
                        }
                        Json::object(fields)
                    })
                    .collect();
                Json::object(vec![
                    ("id", Json::Str(package.id.clone())),
                    ("version", Json::Str(package.version.clone())),
                    (
                        "manifest_sha256",
                        Json::Str(package.manifest_sha256.to_hex()),
                    ),
                    ("tree_sha256", Json::Str(package.tree_sha256.to_hex())),
                    ("entries", Json::Arr(entries)),
                ])
            })
            .collect();
        Json::object(vec![
            ("spec", Json::Str("lexlean/lexicon-closure/1".to_owned())),
            ("module", Json::Str(module.to_owned())),
            ("packages", Json::Arr(packages)),
        ])
    }

    /// Does `category` describe a proof-usable constant (§16.2 `Apply`,
    /// `Close ... with`)?
    #[must_use]
    pub fn is_proof_category(category: Category) -> bool {
        matches!(category, Category::ProofConstant)
    }
}
