//! The linked glossary closure: cross-package validation and the surface
//! index the token lattice matches against (SPEC.md §13.11, §14.1).

use std::collections::{BTreeMap, BTreeSet};

use crate::artifact::canonical_json::Json;
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::lexicon::entry::{surface_safety, Category, Channel, Denotation, Eliminator, Entry};
use crate::lexicon::lse::{self, ConstInfo, Lse, QualifiedId};
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
    /// Core entries by core-denotation constructor, for eliminator lookup
    /// on core-headed types.
    core_constructors: BTreeMap<String, String>,
}

/// The atom-sequence key of a form: class and text of every non-whitespace
/// atom, with whitespace collapsed to one separator (§14.1).
fn surface_key(atoms: &[Atom]) -> Vec<(AtomClass, String)> {
    let mut key = Vec::new();
    for atom in atoms {
        if atom.class == AtomClass::Whitespace {
            if key
                .last()
                .is_some_and(|(class, _)| *class != AtomClass::Whitespace)
            {
                key.push((AtomClass::Whitespace, String::new()));
            }
        } else {
            key.push((atom.class, atom.text.clone()));
        }
    }
    while key
        .last()
        .is_some_and(|(class, _)| *class == AtomClass::Whitespace)
    {
        key.pop();
    }
    key
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

        // Topological order with cycle detection and longest-chain depth,
        // iterative over an explicit stack (the graph depth is user input).
        let mut order: Vec<usize> = Vec::new();
        let mut state: Vec<u8> = vec![0; packages.len()]; // 0 new, 1 open, 2 done
        let mut depth: Vec<u64> = vec![0; packages.len()];
        for root in 0..packages.len() {
            if state[root] == 2 {
                continue;
            }
            // (node, next import index)
            let mut stack: Vec<(usize, usize)> = vec![(root, 0)];
            state[root] = 1;
            while let Some(&mut (node, ref mut next)) = stack.last_mut() {
                if let Some(import) = packages[node].imports.get(*next) {
                    *next += 1;
                    let target = by_id[&import.package];
                    match state[target] {
                        1 => {
                            diagnostics.push(Diagnostic::new(
                                code!("LLR3003"),
                                format!("package import cycle through `{}`", packages[target].id),
                            ));
                            return Err(diagnostics);
                        }
                        2 => {}
                        _ => {
                            state[target] = 1;
                            stack.push((target, 0));
                        }
                    }
                } else {
                    let deepest = packages[node]
                        .imports
                        .iter()
                        .map(|import| depth[by_id[&import.package]].saturating_add(1))
                        .max()
                        .unwrap_or(0);
                    depth[node] = deepest;
                    state[node] = 2;
                    order.push(node);
                    stack.pop();
                    if deepest >= max_import_depth {
                        diagnostics.push(Diagnostic::new(
                            code!("LLS8002"),
                            format!(
                                "max_import_depth exceeded in phase lexicon closure: configured {max_import_depth}, observed import depth {} at package `{}`",
                                deepest.saturating_add(1),
                                packages[node].id
                            ),
                        ));
                    }
                }
            }
        }
        if !diagnostics.is_empty() {
            return Err(diagnostics);
        }
        // Reorder by topological position, core first.
        let ordered: Vec<LexiconPackage> = {
            let mut slots: Vec<Option<LexiconPackage>> = packages.into_iter().map(Some).collect();
            order
                .iter()
                .filter_map(|&index| slots[index].take())
                .collect()
        };
        let package_index: BTreeMap<String, usize> = ordered
            .iter()
            .enumerate()
            .map(|(index, package)| (package.id.clone(), index))
            .collect();

        // Per-package import closure (§13.6, §13.11): a package sees itself
        // and its transitive imports, nothing else — core included only when
        // imported.
        let mut import_closure: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for package in &ordered {
            let mut visible: BTreeSet<String> = BTreeSet::new();
            visible.insert(package.id.clone());
            for import in &package.imports {
                visible.insert(import.package.clone());
                if let Some(transitive) = import_closure.get(&import.package) {
                    visible.extend(transitive.iter().cloned());
                }
            }
            import_closure.insert(package.id.clone(), visible);
        }

        {
            let lookup_any = |id: &QualifiedId| -> Option<&Entry> {
                package_index
                    .get(&id.package)
                    .and_then(|&index| ordered[index].entries.get(&id.entry))
            };

            // Core structural controls, braces, and grammar words are reserved
            // (§12.3): a non-core form that spells one in an overlapping channel
            // is a duplicate of a closed core form. Core punctuation (`-`, `,`,
            // `(`, ...) is not reserved: §13.5 rule 10 lets a mathematical
            // package reuse such a surface (subtraction shares `-` with the
            // hyphen), and its meaning is settled by grammar and type
            // resolution.
            let mut reserved: BTreeMap<Vec<(AtomClass, String)>, (Channel, String)> =
                BTreeMap::new();
            if let Some(core) = package_index.get("lexlean.core").map(|&i| &ordered[i]) {
                for entry in core.entries.values() {
                    let structure = match entry.category {
                        Category::Structural => true,
                        Category::Grammar => false,
                        _ => continue,
                    };
                    for form in &entry.forms {
                        let is_reserved_shape = if structure {
                            form.atoms.iter().any(|atom| {
                                atom.class == AtomClass::Control
                                    || (atom.class == AtomClass::Delimiter
                                        && (atom.text == "{" || atom.text == "}"))
                            })
                        } else {
                            form.atoms.iter().any(|atom| atom.class == AtomClass::Word)
                        };
                        if is_reserved_shape {
                            reserved.entry(surface_key(&form.atoms)).or_insert_with(|| {
                                (form.channel, format!("lexlean.core::{}", entry.id))
                            });
                        }
                    }
                }
                // The bootstrap structural sets and the embedded core agree:
                // every §15.2 control is a canonical `both`-channel form of a
                // core structural entry (an embedded-data invariant).
                for control in &bootstrap.structural.controls {
                    let covered = core.entries.values().any(|entry| {
                        entry.category == Category::Structural
                            && entry.forms.iter().any(|form| {
                                form.canonical_source
                                    && form.channel == Channel::Both
                                    && form.surface == *control
                            })
                    });
                    if !covered {
                        diagnostics.push(Diagnostic::new(
                        code!("LLI9001"),
                        format!(
                            "phase language-load: bootstrap control `{control}` has no core structural entry"
                        ),
                    ));
                    }
                }
            }

            // Cross-entry validation.
            for package in &ordered {
                let visible = &import_closure[&package.id];
                let is_core = package.id == "lexlean.core";
                let resolve = |id: &QualifiedId| -> Result<&Entry, Diagnostic> {
                    match lookup_any(id) {
                        None => Err(Diagnostic::new(
                            code!("LLR3005"),
                            format!("`{id}` does not resolve"),
                        )),
                        Some(_) if !visible.contains(&id.package) => Err(Diagnostic::new(
                            code!("LLR3005"),
                            format!(
                                "`{id}` is outside the import closure of `{}` (imports: [{}])",
                                package.id,
                                package
                                    .imports
                                    .iter()
                                    .map(ToString::to_string)
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ),
                        )),
                        Some(entry) => Ok(entry),
                    }
                };
                let const_info = |id: &QualifiedId| -> ConstInfo<'_> {
                    match lookup_any(id) {
                        Some(entry) if visible.contains(&id.package) => match &entry.signature {
                            Some(signature) => ConstInfo::Signature {
                                signature,
                                defined: matches!(entry.denotation, Denotation::Defined { .. }),
                            },
                            None => ConstInfo::NoSignature,
                        },
                        _ => ConstInfo::Missing,
                    }
                };
                for entry in package.entries.values() {
                    let where_ = format!("{}::{}", package.id, entry.id);
                    let mut resolved = true;
                    let mut expressions: Vec<(&str, &Lse)> = Vec::new();
                    if let Some(signature) = &entry.signature {
                        expressions.push(("signature", signature));
                    }
                    if let Denotation::Defined { value, .. } = &entry.denotation {
                        expressions.push(("defined value", value));
                    }
                    for (what, expression) in &expressions {
                        for reference in expression.referenced_consts() {
                            if let Err(mut diagnostic) = resolve(&reference) {
                                diagnostic.message =
                                    format!("{where_}: {what} references {}", diagnostic.message);
                                diagnostics.push(diagnostic);
                                resolved = false;
                            }
                        }
                    }
                    if resolved {
                        // The conservative checker (§13.7, §14.4): signatures are
                        // types, applications respect explicit arities, defined
                        // values match their signatures.
                        if let Some(signature) = &entry.signature {
                            if let Err(type_error) = lse::check_signature(signature, &const_info) {
                                diagnostics.push(Diagnostic::new(
                                    code!("LLR3004"),
                                    format!(
                                        "{where_}: signature `{}` is not well-typed: {type_error}",
                                        signature.print(false)
                                    ),
                                ));
                            }
                        }
                        if let Denotation::Defined { value, .. } = &entry.denotation {
                            if let Err(type_error) =
                                lse::check_value(value, entry.signature.as_ref(), &const_info)
                            {
                                diagnostics.push(Diagnostic::new(
                                    code!("LLR3004"),
                                    format!(
                                        "{where_}: defined value is not well-typed: {type_error}"
                                    ),
                                ));
                            }
                        }
                    }

                    // Reserved core surfaces (LLR3002).
                    if !is_core {
                        for form in &entry.forms {
                            let Some((core_channel, owner)) =
                                reserved.get(&surface_key(&form.atoms))
                            else {
                                continue;
                            };
                            let overlap = *core_channel == Channel::Both
                                || form.channel == Channel::Both
                                || *core_channel == form.channel;
                            if overlap {
                                diagnostics.push(Diagnostic::new(
                                code!("LLR3002"),
                                format!(
                                    "{where_}: form `{}` duplicates the reserved core surface `{}` of `{owner}`",
                                    form.id, form.surface
                                ),
                            ));
                            }
                        }
                    }

                    // Render templates: tokens exist in the registry with a
                    // channel that covers the template's channel; form references
                    // resolve within the import closure, name an existing form,
                    // and emit only renderer-safe surfaces (§13.9, LLR3006).
                    for (channel, render) in [
                        (Channel::Math, &entry.render_math),
                        (Channel::Text, &entry.render_text),
                    ] {
                        let Some(render) = render else {
                            continue;
                        };
                        let channel_name = if channel == Channel::Text {
                            "text"
                        } else {
                            "math"
                        };
                        for token in render.tokens() {
                            match registry.get(&token) {
                                Some(row) => {
                                    let covers =
                                        row.channel == "both" || row.channel == channel_name;
                                    if !covers {
                                        diagnostics.push(Diagnostic::new(
                                        code!("LLR3004"),
                                        format!(
                                            "{where_}: token `{token}` is a {} token and cannot appear in a {channel_name} render",
                                            row.channel
                                        ),
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
                            match resolve(&entry_ref) {
                            Err(mut diagnostic) => {
                                diagnostic.code = code!("LLR3004");
                                diagnostic.message = format!(
                                    "{where_}: {channel_name} render references {}",
                                    diagnostic.message
                                );
                                diagnostics.push(diagnostic);
                            }
                            Ok(target) => match target.forms.iter().find(|f| f.id == form_id) {
                                None => diagnostics.push(Diagnostic::new(
                                    code!("LLR3004"),
                                    format!(
                                        "{where_}: {channel_name} render references unknown form `{entry_ref}`/`{form_id}`"
                                    ),
                                )),
                                Some(form) => {
                                    if !form.channel.covers(channel) {
                                        diagnostics.push(Diagnostic::new(
                                            code!("LLR3004"),
                                            format!(
                                                "{where_}: {channel_name} render references `{entry_ref}`/`{form_id}`, which is not a {channel_name} form"
                                            ),
                                        ));
                                    }
                                    if let Err(reason) = surface_safety(&form.atoms, form.channel) {
                                        diagnostics.push(Diagnostic::new(
                                            code!("LLR3006"),
                                            format!(
                                                "{where_}: {channel_name} render references `{entry_ref}`/`{form_id}` whose surface `{}` is not renderer-safe: {reason}",
                                                form.surface
                                            ),
                                        ));
                                    }
                                }
                            },
                        }
                        }
                    }

                    // Eliminator descriptors (§16.11): every constructor resolves
                    // within the import closure to an entry whose signature
                    // targets the descriptor's type, with as many fields as
                    // explicit binders and as many induction hypotheses as
                    // recursive fields.
                    if let Some(eliminator) = &entry.eliminator {
                        let self_id = QualifiedId {
                            package: package.id.clone(),
                            entry: entry.id.clone(),
                        };
                        for constructor in &eliminator.constructors {
                            let target = match resolve(&constructor.entry) {
                                Ok(target) => target,
                                Err(diagnostic) => {
                                    diagnostics.push(Diagnostic::new(
                                    code!("LLR3004"),
                                    format!(
                                        "{where_}: eliminator references absent constructor `{}`: {}",
                                        constructor.entry, diagnostic.message
                                    ),
                                ));
                                    continue;
                                }
                            };
                            let Some(signature) = &target.signature else {
                                diagnostics.push(Diagnostic::new(
                                    code!("LLR3004"),
                                    format!(
                                        "{where_}: eliminator constructor `{}` has no signature",
                                        constructor.entry
                                    ),
                                ));
                                continue;
                            };
                            let targets_self = match signature.result() {
                                Lse::Const(id, _) => *id == self_id,
                                Lse::App(function, _) => {
                                    matches!(&**function, Lse::Const(id, _) if *id == self_id)
                                }
                                _ => false,
                            };
                            if !targets_self {
                                diagnostics.push(Diagnostic::new(
                                code!("LLR3004"),
                                format!(
                                    "{where_}: eliminator constructor `{}` does not construct `{self_id}`: its signature results in `{}`",
                                    constructor.entry,
                                    signature.result().print(false)
                                ),
                            ));
                            }
                            let (explicit_fields, recursive_fields) = match signature {
                                Lse::Pi(binders, _) => {
                                    let explicit: Vec<&lse::LseBinder> = binders
                                        .iter()
                                        .filter(|b| b.mode == lse::BinderMode::Explicit)
                                        .collect();
                                    let recursive = explicit
                                        .iter()
                                        .filter(|b| {
                                            let head = match &b.ty {
                                                Lse::App(function, _) => &**function,
                                                other => other,
                                            };
                                            matches!(head, Lse::Const(id, _) if *id == self_id)
                                        })
                                        .count();
                                    (explicit.len(), recursive)
                                }
                                _ => (0, 0),
                            };
                            if constructor.fields.len() != explicit_fields {
                                diagnostics.push(Diagnostic::new(
                                code!("LLR3004"),
                                format!(
                                    "{where_}: eliminator constructor `{}` lists {} field{} but its signature has {explicit_fields} explicit binder{}",
                                    constructor.entry,
                                    constructor.fields.len(),
                                    if constructor.fields.len() == 1 { "" } else { "s" },
                                    if explicit_fields == 1 { "" } else { "s" }
                                ),
                            ));
                            }
                            if constructor.induction_hypotheses.len() != recursive_fields {
                                diagnostics.push(Diagnostic::new(
                                code!("LLR3004"),
                                format!(
                                    "{where_}: eliminator constructor `{}` lists {} induction hypothes{} but has {recursive_fields} recursive field{}",
                                    constructor.entry,
                                    constructor.induction_hypotheses.len(),
                                    if constructor.induction_hypotheses.len() == 1 { "is" } else { "es" },
                                    if recursive_fields == 1 { "" } else { "s" }
                                ),
                            ));
                            }
                        }
                    }
                }
            }
        }

        // Defined-denotation acyclicity (§13.6, LLR3003), iterative.
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
            'roots: for root in edges.keys() {
                if mark.get(root) == Some(&2) {
                    continue;
                }
                let mut stack: Vec<(String, usize)> = vec![(root.clone(), 0)];
                mark.insert(root.clone(), 1);
                while let Some((node, next)) = stack.last().cloned() {
                    let targets = edges.get(&node).map(Vec::as_slice).unwrap_or(&[]);
                    if let Some(target) = targets.get(next) {
                        if let Some(last) = stack.last_mut() {
                            last.1 += 1;
                        }
                        match mark.get(target) {
                            Some(1) => {
                                diagnostics.push(Diagnostic::new(
                                    code!("LLR3003"),
                                    format!("defined-denotation cycle through `{target}`"),
                                ));
                                break 'roots;
                            }
                            Some(2) => {}
                            _ => {
                                mark.insert(target.clone(), 1);
                                stack.push((target.clone(), 0));
                            }
                        }
                    } else {
                        mark.insert(node, 2);
                        stack.pop();
                    }
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
        let mut core_constructors: BTreeMap<String, String> = BTreeMap::new();
        for package in &ordered {
            for entry in package.entries.values() {
                if package.id == "lexlean.core" {
                    if let Denotation::Core { constructor } = &entry.denotation {
                        core_constructors.insert(constructor.clone(), entry.id.clone());
                    }
                }
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
            core_constructors,
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

    /// The core entry that carries the given core-denotation constructor
    /// (for example `logic.and` → `lexlean.core::land`).
    #[must_use]
    pub fn core_entry_for_constructor(&self, constructor: &str) -> Option<QualifiedId> {
        self.core_constructors
            .get(constructor)
            .map(|entry| QualifiedId {
                package: "lexlean.core".to_owned(),
                entry: entry.clone(),
            })
    }

    /// The eliminator descriptor of a type headed by `head`: the entry
    /// itself for a bare constant type, or the head entry of an applied
    /// type (`Or p q` → the descriptor on `lexlean.core::lor`).
    #[must_use]
    pub fn eliminator_for(&self, head: &QualifiedId) -> Option<(&Entry, &Eliminator)> {
        let entry = self.entry(head)?;
        entry
            .eliminator
            .as_ref()
            .map(|eliminator| (entry, eliminator))
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
            if let (Some(last), Some(next)) = (
                source_at.checked_sub(1).and_then(|index| atoms.get(index)),
                atoms.get(source_at),
            ) {
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

/// The token lattice of one module (§14.1): every glossary form beginning
/// at every source position, computed once per `(position, channel)` and
/// counted exactly once against `max_token_lattice_edges`. Every grammar
/// pass that revisits a position shares the memoized edges instead of
/// re-counting; the parse budget owns one lattice per module.
#[derive(Debug)]
pub struct TokenLattice {
    memo: BTreeMap<(usize, Channel), Vec<(FormRef, usize)>>,
    edges: u64,
    max_edges: u64,
}

impl TokenLattice {
    /// An empty lattice bounded by the configured `max_token_lattice_edges`.
    #[must_use]
    pub fn new(max_token_lattice_edges: u64) -> Self {
        Self {
            memo: BTreeMap::new(),
            edges: 0,
            max_edges: max_token_lattice_edges,
        }
    }

    /// The edges beginning at `start` in `channel` over the module's atoms
    /// and visible packages. The first request for a position computes and
    /// counts them (`LLS8002` past the limit); later requests are free.
    pub fn edges_at(
        &mut self,
        closure: &Closure,
        atoms: &[Atom],
        visible: &BTreeSet<String>,
        start: usize,
        channel: Channel,
    ) -> Result<&[(FormRef, usize)], Diagnostic> {
        if !self.memo.contains_key(&(start, channel)) {
            let found = closure.matches_at(atoms, start, channel, visible);
            self.edges = self.edges.saturating_add(found.len() as u64);
            if self.edges > self.max_edges {
                return Err(Diagnostic::new(
                    code!("LLS8002"),
                    format!(
                        "max_token_lattice_edges exceeded in phase lexical resolution: configured {}, observed {} distinct lattice edges",
                        self.max_edges, self.edges
                    ),
                ));
            }
            self.memo.insert((start, channel), found);
        }
        Ok(self
            .memo
            .get(&(start, channel))
            .map(Vec::as_slice)
            .unwrap_or(&[]))
    }

    /// The number of distinct edges counted so far.
    #[must_use]
    pub fn edge_count(&self) -> u64 {
        self.edges
    }
}
