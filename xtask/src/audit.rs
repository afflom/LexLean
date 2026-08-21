//! The repository audits (SPEC.md §27.10). Crude on purpose: each reads the
//! source, finds the defect, and fails naming the rule it enforces.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use crate::Fail;

const SKIP_DIRS: [&str; 5] = ["target", ".git", ".lexlean", "expected", "node_modules"];

fn gather(root: &Path, dirs: &[&str], extensions: &[&str], out: &mut Vec<PathBuf>) {
    for dir in dirs {
        let base = root.join(dir);
        if !base.exists() {
            continue;
        }
        for entry in walkdir::WalkDir::new(&base)
            .follow_links(false)
            .into_iter()
            .flatten()
        {
            if entry.file_type().is_dir() {
                continue;
            }
            let path = entry.path();
            if path.components().any(|component| {
                SKIP_DIRS.contains(&component.as_os_str().to_string_lossy().as_ref())
            }) {
                continue;
            }
            let name = path.file_name().unwrap_or_default().to_string_lossy();
            if extensions.iter().any(|extension| name.ends_with(extension)) {
                out.push(path.to_path_buf());
            }
        }
    }
    for entry in std::fs::read_dir(root).into_iter().flatten().flatten() {
        let path = entry.path();
        if path.extension().is_some_and(|extension| extension == "md") {
            out.push(path);
        }
    }
    out.sort();
    out.dedup();
}

/// Decode the committed Atlas source itself.  Coverage gates deliberately
/// enter through this function: the migration oracle can prove equivalence,
/// but it cannot define which declarations the released LexLean corpus owns.
fn atlas_source_core(root: &Path) -> Result<lexlean::ir::core::CoreModule, Fail> {
    let path = root.join("examples/uor-atlas/src/Atlas.lex.tex");
    let source =
        std::fs::read_to_string(&path).map_err(|error| format!("{}: {error}", path.display()))?;
    let marker = "\\coredata{";
    let start = source.find(marker).ok_or_else(|| {
        Fail::from(format!(
            "R4: {} has no native core payload; the Atlas source must arm its own coverage audit",
            path.display()
        ))
    })? + marker.len();
    let tail = &source[start..];
    let end = tail.find("}\n\\end{coremodule}").ok_or_else(|| {
        Fail::from(format!(
            "R4: {} has no closed native core module",
            path.display()
        ))
    })?;
    lexlean::ir::core::CoreModule::parse(&tail[..end])
        .map_err(|reason| format!("R4: {}: {reason}", path.display()).into())
}

/// The repository root files and dot-directories with a defined role
/// (SPEC.md §7): the audits read them too, so a deferral cannot park in
/// a manifest, a lint configuration, the Justfile, the container, or a
/// workflow.
///
/// §7 admits an additional file only when it has a defined role *and* the
/// repository audits include it, so every root file this repository adds
/// beyond the §7 tree is named here. A file added without its line would be
/// the one place in the tree a deferral could sit unread.
fn root_tooling(root: &Path, out: &mut Vec<PathBuf>) {
    for name in [
        "Cargo.toml",
        "deny.toml",
        "clippy.toml",
        "rustfmt.toml",
        "rust-toolchain.toml",
        "lean-toolchain",
        "Justfile",
        ".gitignore",
        ".gitattributes",
        ".dockerignore",
        "Dockerfile",
        ".cargo/config.toml",
        ".devcontainer/devcontainer.json",
    ] {
        let path = root.join(name);
        if path.is_file() {
            out.push(path);
        }
    }
    for entry in std::fs::read_dir(root.join(".github/workflows"))
        .into_iter()
        .flatten()
        .flatten()
    {
        if entry.path().is_file() {
            out.push(entry.path());
        }
    }
    out.sort();
    out.dedup();
}

/// Does `marker` occur in `line` outside every backtick-delimited span?
fn outside_code_spans(line: &str, marker: &str) -> bool {
    let mut at = 0usize;
    while let Some(position) = line[at..].find(marker) {
        let absolute = at + position;
        if line[..absolute].matches('`').count().is_multiple_of(2) {
            return true;
        }
        at = absolute + marker.len();
    }
    false
}

/// The completed Atlas migration oracle carries no `sorry`, `admit`, author-declared
/// `axiom`, `opaque`, `unsafe`, or `native_decide` (release plan §4.4; §8
/// names each of them an explicit non-deferral).
///
/// The library is repository content built by `just vv`, so this is a
/// standing gate rather than a one-time measurement: checked once is checked
/// never on the next commit. The word list is
/// [`lexlean::verify::source_audit`]'s, so the spelling cannot drift from the
/// generated-Lean audit that already enforces §18.2.
///
/// # Errors
/// Returns the offending module and token, or reports the gate armed when no
/// library module exists yet --- an empty register that passed silently would
/// read as evidence.
pub fn audit_atlas_library(root: &Path) -> Result<(), Fail> {
    let mut files = Vec::new();
    gather(root, &["lean"], &[".lean"], &mut files);
    // `gather` also sweeps the root's Markdown for the documentation audits;
    // this gate reads Lean modules only.
    files.retain(|path| {
        path.extension()
            .is_some_and(|extension| extension == "lean")
    });
    files.sort();
    if files.is_empty() {
        println!(
            "audit-atlas-library: no migration-oracle module; the gate is armed by the first one"
        );
        return Ok(());
    }
    for path in &files {
        let text = std::fs::read_to_string(path)
            .map_err(|error| Fail::from(format!("{}: {error}", path.display())))?;
        if let Err(reason) = lexlean::verify::source_audit::audit_library(&text) {
            return Err(Fail::from(format!(
                "R4: {}: {reason}; the Atlas migration oracle admits none of them",
                path.display()
            )));
        }
    }
    unreachable_library_modules(root, &files)?;
    println!(
        "audit-atlas-library: {} vendored Lean modules, none names a forbidden construct, every one reachable from the library root (R4)",
        files.len()
    );
    Ok(())
}

/// Every module of the migration oracle is reachable from its root module.
///
/// The axiom gate walks the environment the root pulls in, so a module sitting
/// in the tree that nothing imports would be scanned for forbidden words and
/// never checked for axioms --- a hole exactly the shape of the thing the gate
/// exists to catch. The audit harness under `audit/` is deliberately outside
/// the library and is excluded.
fn unreachable_library_modules(root: &Path, files: &[PathBuf]) -> Result<(), Fail> {
    let base = root.join("lean/uor-atlas");
    let module_of = |path: &Path| -> Option<String> {
        let rel = path.strip_prefix(&base).ok()?;
        let text = rel.to_string_lossy();
        let stem = text.strip_suffix(".lean")?;
        Some(stem.replace(['/', '\\'], "."))
    };
    let library: BTreeSet<String> = files
        .iter()
        .filter(|path| !path.starts_with(base.join("audit")))
        .filter_map(|path| module_of(path))
        .collect();
    if library.is_empty() {
        return Ok(());
    }
    let mut reached: BTreeSet<String> = BTreeSet::new();
    let mut stack = vec!["UorAtlas".to_owned()];
    while let Some(name) = stack.pop() {
        if !reached.insert(name.clone()) {
            continue;
        }
        let path = base.join(format!("{}.lean", name.replace('.', "/")));
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        for line in text.lines() {
            let rest = line
                .strip_prefix("public import ")
                .or_else(|| line.strip_prefix("import "));
            if let Some(target) = rest {
                let target = target.trim();
                if target.starts_with("UorAtlas") {
                    stack.push(target.to_owned());
                }
            }
        }
    }
    let orphans: Vec<&String> = library.difference(&reached).collect();
    if orphans.is_empty() {
        return Ok(());
    }
    Err(Fail::from(format!(
        "R4: the Atlas migration oracle has {} module(s) no import reaches from `UorAtlas`, so the equivalence export never sees them: {}",
        orphans.len(),
        orphans
            .iter()
            .map(|name| name.as_str())
            .collect::<Vec<&str>>()
            .join(", ")
    )))
}

/// No two *spellable* entries share a surface in a channel (release plan
/// §2.4, which makes this the SPEC.md §30.2 compliance condition rather than
/// hygiene).
///
/// `fmt` emits a bare surface only when exactly one visible entry owns it in
/// that channel, so a second owner silently promotes a previously-bare
/// spelling to its qualified form and breaks the byte-identical canonical
/// output §30.2 requires. `structural` and `grammar` entries are excluded
/// because they are the parser's own layer: they are consumed as document
/// structure and never resolved as term atoms, which is why `-` can be both
/// `lexlean.core::hyphen` and `lexlean.std.nat::sub` today without either
/// losing a spelling. Those overlaps are counted and reported rather than
/// hidden, because §10 records disjointness as a snapshot a later entry can
/// reopen.
///
/// # Errors
/// Returns the colliding surface and its owners, or reports the gate armed
/// when no package carries a spellable form yet.
pub fn audit_surface_disjointness(_root: &Path) -> Result<(), Fail> {
    use lexlean::lexicon::entry::{Category, Channel};

    let bootstrap = lexlean::lexicon::load_bootstrap()
        .map_err(|diagnostic| Fail::from(diagnostic.message.clone()))?;
    let ctx = lexlean::lexicon::package::LoadContext {
        forbidden_controls: &bootstrap.structural.forbidden_controls,
        max_scope_depth: 1024,
    };
    let mut spellable: std::collections::BTreeMap<(Channel, String), BTreeSet<String>> =
        std::collections::BTreeMap::new();
    let mut parser_layer: std::collections::BTreeMap<(Channel, String), BTreeSet<String>> =
        std::collections::BTreeMap::new();
    for row in &bootstrap.builtin_packages {
        let package = lexlean::lexicon::load_builtin_package(row, &ctx).map_err(|diagnostics| {
            Fail::from(
                diagnostics
                    .iter()
                    .map(|diagnostic| diagnostic.message.clone())
                    .collect::<Vec<String>>()
                    .join("; "),
            )
        })?;
        for (entry_id, entry) in &package.entries {
            let qualified = format!("{}::{entry_id}", package.id);
            let parser_own = matches!(entry.category, Category::Structural | Category::Grammar);
            for form in &entry.forms {
                for channel in [Channel::Text, Channel::Math] {
                    if !form.channel.covers(channel) {
                        continue;
                    }
                    let key = (channel, form.surface.clone());
                    if parser_own {
                        parser_layer
                            .entry(key)
                            .or_default()
                            .insert(qualified.clone());
                    } else {
                        spellable.entry(key).or_default().insert(qualified.clone());
                    }
                }
            }
        }
    }
    if spellable.is_empty() {
        println!(
            "audit-surface-disjointness: no package carries a spellable form; the gate is armed by the first one"
        );
        return Ok(());
    }
    if let Some(((channel, surface), owners)) =
        spellable.iter().find(|(_, owners)| owners.len() > 1)
    {
        return Err(Fail::from(format!(
            "R7: the surface `{surface}` is owned by {} entries in the {channel:?} channel ({}); `fmt` spells a surface bare only when one visible entry owns it, so a second owner changes canonical output and breaks §30.2 byte-compatibility",
            owners.len(),
            owners.iter().cloned().collect::<Vec<String>>().join(", ")
        )));
    }
    let overlaps = parser_layer
        .iter()
        .filter(|(key, _)| spellable.contains_key(key) || parser_layer[key].len() > 1)
        .count();
    println!(
        "audit-surface-disjointness: {} spellable surfaces across {} builtin packages, no two entries share one in a channel; {overlaps} parser-layer overlap(s) recorded (R7)",
        spellable.len(),
        bootstrap.builtin_packages.len()
    );
    Ok(())
}

/// The Atlas label registers partition the labels owned by the committed
/// native Atlas source, every live row has a source declaration, and no source
/// declaration claims a label the registers withhold.
///
/// The registers key on EXACT identifiers. That is the whole point of §2.8's
/// "exact-match semantics": `T57` is retracted while `T57a`..`T57c` are live,
/// `T10` is superseded while `T10a`..`T10c` are live, and `F8`..`F11` are
/// retracted while `F1`..`F7` and `F12` are live, so a register that matched by
/// prefix would reject exactly the live labels it exists to admit.
///
/// A label may be declared exactly once in the whole library, including twice
/// within one module: Lean permits `SpecSys.RC1` beside `RC1` because their
/// qualified names differ, but a pack entry denoting `RC1` then has two
/// constants to choose between, which is ambiguity rather than redundancy.
///
/// # Errors
/// Returns the offending label, or reports the gate armed when the registers
/// carry no row yet.
pub fn audit_atlas_registers(root: &Path) -> Result<(), Fail> {
    let path = root.join("language/uor/atlas-registers.toml");
    if !path.exists() {
        println!("audit-atlas-registers: no register file; the gate is armed by the first one");
        return Ok(());
    }
    let text = std::fs::read_to_string(&path)?;
    let data: toml::Value = text.parse()?;
    let list = |key: &str| -> BTreeSet<String> {
        data.get(key)
            .and_then(|value| value.as_array())
            .map(|items| {
                items
                    .iter()
                    .filter_map(|item| item.as_str())
                    .map(str::to_owned)
                    .collect()
            })
            .unwrap_or_default()
    };
    let rows = |key: &str| -> BTreeSet<String> {
        data.get(key)
            .and_then(|value| value.as_array())
            .map(|items| {
                items
                    .iter()
                    .filter_map(|item| item.get("label").and_then(|label| label.as_str()))
                    .map(str::to_owned)
                    .collect()
            })
            .unwrap_or_default()
    };
    let entry = list("entry");
    let ambient = list("ambient");
    let non_denotable = list("non_denotable");
    let retracted = rows("retracted");
    let superseded = rows("superseded");
    if entry.is_empty() {
        println!("audit-atlas-registers: the entry register is empty; the gate is armed by the first row");
        return Ok(());
    }

    // The four dispositions are a partition: no label may carry two.
    let named: [(&str, &BTreeSet<String>); 5] = [
        ("entry", &entry),
        ("ambient", &ambient),
        ("non-denotable", &non_denotable),
        ("retracted", &retracted),
        ("superseded", &superseded),
    ];
    for (i, (left_name, left)) in named.iter().enumerate() {
        for (right_name, right) in named.iter().skip(i + 1) {
            if let Some(both) = left.intersection(right).next() {
                return Err(Fail::from(format!(
                    "R4: `{both}` is in both the {left_name} and {right_name} registers; §2.8 gives every label exactly one disposition"
                )));
            }
        }
    }

    // A declaration may not claim a label the registers withhold. Only the
    // final name segment is considered, so supporting declarations are not
    // forced into the document-label register.
    let withheld: BTreeSet<String> = retracted
        .iter()
        .chain(superseded.iter())
        .chain(non_denotable.iter())
        .cloned()
        .collect();
    let live: BTreeSet<String> = entry.iter().chain(ambient.iter()).cloned().collect();
    let core = atlas_source_core(root)?;
    let mut declared: BTreeMap<String, String> = BTreeMap::new();
    let mut lookalike: Vec<String> = Vec::new();
    for declaration in &core.declarations {
        let name = declaration
            .name
            .rsplit('.')
            .next()
            .unwrap_or(&declaration.name);
        if !is_label_shaped(name) {
            continue;
        }
        if withheld.contains(name) {
            return Err(Fail::from(format!(
                "R4: the native Atlas source declares `{}`, which the registers withhold (retracted, superseded, or non-denotable)",
                declaration.name
            )));
        }
        if live.contains(name) {
            if let Some(first) = declared.insert(name.to_owned(), declaration.name.clone()) {
                return Err(Fail::from(format!(
                    "R4: `{name}` is declared as both `{first}` and `{}` in the native Atlas source; one label has one declaration",
                    declaration.name
                )));
            }
        } else {
            lookalike.push(declaration.name.clone());
        }
    }
    let missing: Vec<&str> = live
        .iter()
        .filter(|label| !declared.contains_key(label.as_str()))
        .map(String::as_str)
        .collect();
    if !missing.is_empty() {
        return Err(Fail::from(format!(
            "R4: the Atlas register has {} live label(s) absent from the native Atlas source: {}; a live source row is an obligation, not an optional description of what was migrated",
            missing.len(),
            missing.join(", ")
        )));
    }
    println!(
        "audit-atlas-registers: {} labels registered ({} entry, {} ambient, {} withheld), dispositions disjoint, all {} live labels rooted in the native Atlas source",
        entry.len() + ambient.len() + non_denotable.len() + retracted.len() + superseded.len(),
        entry.len(),
        ambient.len(),
        non_denotable.len() + retracted.len() + superseded.len(),
        entry.len() + ambient.len(),
    );
    if !lookalike.is_empty() {
        println!(
            "audit-atlas-registers: {} source name(s) are label-shaped support names rather than registered labels: {}",
            lookalike.len(),
            lookalike.join(", ")
        );
    }
    Ok(())
}

/// Is this identifier shaped like a document label --- one or two capitals then
/// digits, optionally with a lower-case suffix (`T57a`, `V65c`, `T59p0`)?
fn is_label_shaped(name: &str) -> bool {
    let letters = name.chars().take_while(char::is_ascii_uppercase).count();
    if letters == 0 || letters > 2 || name.len() == letters {
        return false;
    }
    let rest = &name[letters..];
    rest.starts_with(|c: char| c.is_ascii_digit())
        && rest.chars().all(|c| c.is_ascii_alphanumeric())
}

/// Every Lean denotation of the frozen Atlas package names a declaration in
/// the native Atlas source, and every live source label has exactly one entry
/// denoting it (R2, R4).
///
/// The crate's own `builtin_lean_names_are_conservative_and_known` checks the
/// *shape* of these names and cannot check more: the shipped compiler carries
/// the language data, not the Lean sources, so nothing inside the crate can
/// see a project's source. This gate is the other half. Without it an entry could denote
/// `UorAtlas.Roots.T5` after `T5` was renamed or withdrawn, and the pack would
/// go on advertising a result the native corpus no longer owns.
///
/// It compares in both directions on purpose. A denotation with no
/// declaration is a claim with nothing behind it; a declaration with no entry
/// is a label the library proves and the pack silently withholds, which is the
/// same coverage lie told the other way round.
pub fn audit_atlas_denotations(root: &Path) -> Result<(), Fail> {
    let entries_dir = root.join("language/uor/atlas/entries");
    if !entries_dir.exists() {
        return Err(Fail::from(
            "R4: the frozen Atlas package is absent while the Atlas source is registered",
        ));
    }
    let core = atlas_source_core(root)?;
    let declared: BTreeSet<&str> = core
        .declarations
        .iter()
        .map(|declaration| declaration.name.as_str())
        .collect();

    // The registers, read before the entries so every entry's identity can be
    // checked against them. An entry's id carries its label -- `atlas-t57a` is
    // `T57a` -- and the label must be one the document still stands behind.
    // Checking the *denotation* instead would never reach a withdrawn label,
    // because the library does not declare one: the guard would be unreachable
    // and would sit there looking like protection it could not give.
    let registers = root.join("language/uor/atlas-registers.toml");
    let mut live_labels: Option<BTreeSet<String>> = None;
    let mut withdrawn: BTreeMap<String, String> = BTreeMap::new();
    if registers.exists() {
        let data: toml::Value = std::fs::read_to_string(&registers)?.parse()?;
        let mut live: BTreeSet<String> = BTreeSet::new();
        for key in ["entry", "ambient"] {
            if let Some(items) = data.get(key).and_then(toml::Value::as_array) {
                live.extend(items.iter().filter_map(|i| i.as_str()).map(str::to_owned));
            }
        }
        if let Some(items) = data.get("non_denotable").and_then(toml::Value::as_array) {
            for label in items.iter().filter_map(|i| i.as_str()) {
                withdrawn.insert(label.to_owned(), "non-denotable".to_owned());
            }
        }
        for (key, why) in [("retracted", "retracted"), ("superseded", "superseded")] {
            if let Some(items) = data.get(key).and_then(toml::Value::as_array) {
                for row in items {
                    if let Some(label) = row.get("label").and_then(toml::Value::as_str) {
                        withdrawn.insert(label.to_owned(), why.to_owned());
                    }
                }
            }
        }
        live_labels = Some(live);
    }

    // Every Lean denotation the package makes.
    let mut files: Vec<PathBuf> = Vec::new();
    gather(
        root,
        &["language/uor/atlas/entries"],
        &[".toml"],
        &mut files,
    );
    // `gather` also sweeps the root's own `.md` files, so the extension filter
    // has to be reapplied here rather than trusted from the call.
    files.retain(|path| path.extension().is_some_and(|e| e == "toml"));
    files.sort();

    if declared.is_empty() || files.is_empty() {
        return Err(Fail::from(format!(
            "R4: audit-atlas-denotations scanned {} native declaration(s) and {} entry file(s); a gate that inspects nothing cannot pass",
            declared.len(),
            files.len()
        )));
    }
    let mut denoted: BTreeSet<String> = BTreeSet::new();
    for path in &files {
        let data: toml::Value = std::fs::read_to_string(path)?.parse()?;
        let Some(denotation) = data.get("denotation") else {
            continue;
        };
        if denotation.get("kind").and_then(toml::Value::as_str) != Some("lean") {
            continue;
        }
        let module = denotation
            .get("module")
            .and_then(toml::Value::as_str)
            .unwrap_or_default();
        let name = denotation
            .get("name")
            .and_then(toml::Value::as_str)
            .unwrap_or_default();
        let bare = name.rsplit('.').next().unwrap_or_default().to_owned();
        let display = path.file_name().unwrap_or_default().to_string_lossy();
        // `atlas-t57a` names the label `T57a`: the leading run of letters is
        // the label's prefix and is upper case, the rest is as written. An id
        // with no digit names no label --- those are the entries for the
        // *objects* a live definition introduces, `atlas-presentation` for
        // `D17` and the rest of that chain, which the document does not label
        // and which are checked here only for having a real denotation.
        if let Some(stem) = display
            .strip_suffix(".toml")
            .and_then(|s| s.strip_prefix("atlas-"))
            .filter(|stem| stem.chars().any(|c| c.is_ascii_digit()))
        {
            let split = stem
                .find(|c: char| !c.is_ascii_alphabetic())
                .unwrap_or(stem.len());
            let label = format!("{}{}", stem[..split].to_ascii_uppercase(), &stem[split..]);
            if let Some(why) = withdrawn.get(&label) {
                return Err(Fail::from(format!(
                    "R2: `{display}` is an entry for `{label}`, which the register records as {why}; a document could cite it as though it stood"
                )));
            }
            if let Some(live) = &live_labels {
                if !live.contains(&label) {
                    return Err(Fail::from(format!(
                        "R2: `{display}` is an entry for `{label}`, which is not a live label of the document"
                    )));
                }
            }
        }
        if !name.starts_with(&format!("{module}.")) || !declared.contains(name) {
            return Err(Fail::from(format!(
                "R2: `{display}` denotes `{name}` in `{module}`, which the native Atlas source does not declare"
            )));
        }
        // One entry per label, counted among the label entries only. An object
        // entry denotes the same Lean declaration as the label that introduces
        // it --- `atlas-presentation` and `atlas-d17` both name
        // `UorAtlas.Blocks.D17` --- because the document labels the definition
        // and the definition introduces the object. That is two entries for one
        // declaration on purpose, and not two entries for one label.
        let label_entry = display
            .strip_suffix(".toml")
            .and_then(|s| s.strip_prefix("atlas-"))
            .is_some_and(|stem| stem.chars().any(|c| c.is_ascii_digit()));
        if label_entry && !denoted.insert(bare.clone()) {
            return Err(Fail::from(format!(
                "R4: `{bare}` is denoted by more than one label entry; one label, one entry"
            )));
        }
    }

    // The other direction: a live source label the frozen pack withholds.
    if let Some(live) = &live_labels {
        for label in live {
            if !denoted.contains(label) {
                return Err(Fail::from(format!(
                    "R4: the native Atlas source declares live label `{label}` and no frozen entry denotes it"
                )));
            }
        }
    }

    println!(
        "audit-atlas-denotations: {} live Atlas labels, every frozen Lean denotation rooted in the native Atlas source (R2, R4)",
        denoted.len()
    );
    Ok(())
}

/// The native Atlas module is the sole example entrypoint, every theorem root
/// is classified as proof data, and no frozen entry surface prefixes another
/// (R4, R7).
///
/// *Prefix-freeness.* A surface that is a prefix of another can be extended by
/// a word from any other visible package into a second complete parse, and the
/// document then has two linked interpretations (`LLP2002`). It is not
/// hypothetical: `T59p`'s surface followed by `std.nat`'s `zero` read as
/// `T59p0`, and the exhaustive module was rejected until every Atlas surface
/// was made prefix-free by a closing word. Surface disjointness is §2.4's
/// compatibility condition, and mere pairwise distinctness does not give it.
pub fn audit_atlas_exercise(root: &Path) -> Result<(), Fail> {
    let entries_dir = root.join("language/uor/atlas/entries");
    if !entries_dir.exists() {
        return Err(Fail::from(
            "R4: the frozen Atlas package is absent while the Atlas source is registered",
        ));
    }
    let mut files: Vec<PathBuf> = Vec::new();
    gather(
        root,
        &["language/uor/atlas/entries"],
        &[".toml"],
        &mut files,
    );
    files.retain(|path| path.extension().is_some_and(|e| e == "toml"));
    files.sort();
    if files.is_empty() {
        return Err(Fail::from(
            "R4: audit-atlas-exercise found no entry files; a gate that inspects nothing cannot pass"
                .to_owned(),
        ));
    }

    let mut surfaces: Vec<(String, String)> = Vec::new();
    for path in &files {
        let data: toml::Value = std::fs::read_to_string(path)?.parse()?;
        let id = data
            .get("id")
            .and_then(toml::Value::as_str)
            .unwrap_or_default()
            .to_owned();
        let surface = data
            .get("form")
            .and_then(toml::Value::as_array)
            .and_then(|forms| forms.first())
            .and_then(|form| form.get("surface"))
            .and_then(toml::Value::as_str)
            .unwrap_or_default()
            .to_owned();
        if id.is_empty() || surface.is_empty() {
            return Err(Fail::from(format!(
                "R4: {} has no id or no canonical surface",
                path.display()
            )));
        }
        surfaces.push((id, surface));
    }

    for (id, surface) in &surfaces {
        for (other_id, other) in &surfaces {
            if id != other_id && other.starts_with(&format!("{surface} ")) {
                return Err(Fail::from(format!(
                    "R7: `{id}`'s surface is a prefix of `{other_id}`'s; a following word from another package would make a second complete parse"
                )));
            }
        }
    }

    let config: toml::Value =
        std::fs::read_to_string(root.join("examples/uor-atlas/lexlean.toml"))?.parse()?;
    let entrypoints: Vec<&str> = config
        .get("entrypoints")
        .and_then(toml::Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(toml::Value::as_str)
        .collect();
    if entrypoints != ["src/Atlas.lex.tex"] {
        return Err(Fail::from(format!(
            "R4: the Atlas example entrypoints are {entrypoints:?}; the native Atlas source must be the sole coverage root"
        )));
    }

    let core = atlas_source_core(root)?;
    if core
        .imports
        .iter()
        .any(|module| module == "UorAtlas" || module.starts_with("UorAtlas."))
    {
        return Err(Fail::from(
            "R8: the native Atlas source imports the handwritten migration oracle",
        ));
    }
    let proof_nodes: BTreeSet<usize> = core.proof_nodes.iter().copied().collect();
    for declaration in &core.declarations {
        if matches!(declaration.kind, lexlean::ir::core::CoreDeclKind::Theorem)
            && !declaration
                .value
                .is_some_and(|value| proof_nodes.contains(&value))
        {
            return Err(Fail::from(format!(
                "R4: native Atlas theorem `{}` has no classified proof root",
                declaration.name
            )));
        }
    }

    println!(
        "audit-atlas-exercise: {} frozen entries are prefix-free; the sole Atlas entrypoint owns {} declarations and all theorem proofs (R4, R7, R8)",
        surfaces.len(),
        core.declarations.len()
    );
    Ok(())
}

/// An authority cites something this repository does not establish, so no row
/// may name repository content (R2, SPEC.md §27.4).
///
/// The distinction is the one AGENTS.md draws: a claim about a dependency
/// belongs to that dependency, and a claim about what is in this tree is a
/// `build` claim with a conformance ID, not a `some-true` citation. The check
/// reads the citation up to its first semicolon --- its primary reference ---
/// because a legitimate row may go on to name repository fixtures as the
/// evidence a third party compares against, which `PRINT-AXIOMS-4-32-1` does.
///
/// # Errors
/// Returns the offending row, or reports the gate armed when no row exists.
pub fn audit_authority_scope(root: &Path) -> Result<(), Fail> {
    let text = std::fs::read_to_string(root.join("model/authorities.toml"))?;
    let data: toml::Value = text.parse()?;
    let Some(rows) = data.get("authority").and_then(|value| value.as_array()) else {
        println!("audit-authority-scope: no authority row; the gate is armed by the first one");
        return Ok(());
    };
    if rows.is_empty() {
        println!(
            "audit-authority-scope: the register is empty; the gate is armed by the first row"
        );
        return Ok(());
    }
    for row in rows {
        let id = row
            .get("id")
            .and_then(|v| v.as_str())
            .unwrap_or("<unnamed>");
        let citation = row
            .get("citation")
            .and_then(|v| v.as_str())
            .unwrap_or_default();
        let primary = citation.split(';').next().unwrap_or_default().trim();
        if primary.to_ascii_lowercase().contains("in this repository") {
            return Err(Fail::from(format!(
                "R2: authority `{id}` cites repository content; what this repository builds is a `build` claim with a conformance ID, never a `some-true` citation (§27.4)"
            )));
        }
        for word in primary.split(|c: char| c.is_whitespace() || c == ',') {
            let candidate = word.trim_matches(|c: char| {
                !c.is_ascii_alphanumeric() && c != '/' && c != '.' && c != '-' && c != '_'
            });
            if candidate.is_empty() || !candidate.contains('/') || candidate.contains("://") {
                continue;
            }
            if root.join(candidate).exists() {
                return Err(Fail::from(format!(
                    "R2: authority `{id}` cites `{candidate}`, which is a path in this repository; an authority is what this repository does not establish (§27.4)"
                )));
            }
        }
    }
    println!(
        "audit-authority-scope: {} authority rows, none cites repository content (R2)",
        rows.len()
    );
    Ok(())
}

/// No two modules of the migration oracle state the same theorem.
///
/// Lean rejects a repeated fully-qualified name, so what survives compilation
/// is the same statement proved twice under two namespaces --- which is what
/// happened to `sumInt_congr`, proved in `Glue` and again in `Roots`, which
/// imports it. A second proof of a settled fact is not merely untidy: it is a
/// second thing to keep true, and the two can drift.
///
/// The comparison is the declaration's name together with the conclusion of
/// its statement, whitespace-normalized. Binders differ freely between two
/// spellings of one lemma --- one module binds `{n : Nat}` where another takes
/// it from a section variable --- so comparing whole statements misses exactly
/// the redundancy this gate exists to find, while comparing conclusions catches
/// it and still lets two genuinely different lemmas share a name, as
/// `Linear.neg_add` and `NumInstances.neg_add` did.
///
/// What it does not catch, stated so nobody reads more into a green line than
/// it carries: the conclusions are compared as text, so the same lemma written
/// once fully qualified and once through an `open` reads as two. This gate
/// narrows duplication; it does not decide it.
///
/// # Errors
/// Returns the repeated statement and the modules that carry it, or reports the
/// gate armed when the library has no module yet.
pub fn audit_atlas_duplication(root: &Path) -> Result<(), Fail> {
    let mut files = Vec::new();
    gather(root, &["lean"], &[".lean"], &mut files);
    files.retain(|path| {
        path.extension()
            .is_some_and(|extension| extension == "lean")
    });
    files.sort();
    if files.is_empty() {
        println!("audit-atlas-duplication: no vendored module; the gate is armed by the first one");
        return Ok(());
    }
    let mut seen: std::collections::BTreeMap<String, (String, String)> =
        std::collections::BTreeMap::new();
    // Keyed on the conclusion alone, so a fact re-proved under a *different*
    // name is caught too. Keying on `name :: conclusion` misses exactly the
    // case that keeps happening: `imgSet` and its five lemmas were a complete
    // duplicate of `actP` and its lemmas, invisible here because only the
    // names differed, and `dotTri` was re-proved in a second module on purpose.
    // Re-proving locally is never the fix; importing is, and when there is no
    // common home, moving the fact down to one is the task.
    let mut by_conclusion: std::collections::BTreeMap<String, (String, String, String)> =
        std::collections::BTreeMap::new();
    let mut counted = 0usize;
    let mut review: Vec<String> = Vec::new();
    for path in &files {
        let text = std::fs::read_to_string(path)?;
        let module = path
            .strip_prefix(root)
            .unwrap_or(path)
            .to_string_lossy()
            .into_owned();
        for (name, signature, statement, is_theorem, body) in public_statements(&text) {
            counted += 1;
            // Keyed on the FULL signature, not the conclusion. `conclusion_of`
            // strips binders, so two different functions that share a name and a
            // return type --- `blkIdx (a b c d : Nat) : Nat` searching a table
            // and `blkIdx (i : Nat) : Nat` reading a packed byte --- would read
            // as one declaration and the gate would report a duplicate that is
            // only a name collision.
            let key = format!("{name} :: {signature}");
            if let Some((first_module, _)) = seen.get(&key) {
                // Reported whether or not the two are in the same file. Keying
                // the report on `first_module != module` made every same-file
                // duplicate invisible, and the modules this gate reads run to
                // six thousand lines --- the file where a redundant lemma is
                // *most* likely to be written twice is the one too long to hold
                // in view.
                let where_ = if *first_module == module {
                    format!("twice in {module}")
                } else {
                    format!("in {first_module} and {module}")
                };
                return Err(Fail::from(format!(
                    "R4: `{name}` is stated identically {where_}; one proof of a settled fact, not two that can drift"
                )));
            } else {
                seen.insert(key, (module.clone(), name.clone()));
            }
            // Only theorems, and only conclusions that name something. A
            // `def ... : Prop` concludes `Prop`, and an extensionality lemma
            // concludes `a = b`; both are shapes shared by unrelated results,
            // and matching on them reports nothing but noise. Requiring a
            // qualified name in the conclusion keeps the check on statements
            // that are *about* a specific object, which is what a re-proved
            // fact looks like. It is a net rather than a proof: a duplicate
            // written entirely in opened names would slip through, and only
            // reading catches that one.
            if !is_theorem || !statement.contains('.') {
                continue;
            }
            if let Some((first_module, first_name, first_body)) = by_conclusion.get(&statement) {
                // What R4 forbids is a second *proof*, so the proof is what
                // this compares. Two exemptions follow from that, and both are
                // real cases in this library rather than hypotheticals.
                //
                // Delegation: `T79`'s proof is `F6 L v g x`. Section 13 and
                // section 19.5 name one equation twice, so one proof carries
                // two document labels --- that is compliance, not a breach.
                //
                // A different argument: `aut_fix_trivial` and `autA_trivial`
                // both conclude `g = Perm.one 120`, one by sifting a stabiliser
                // chain from `D21 g` and one by profile pinning from `AutA g`.
                // Neither can be derived from the other without circularity,
                // because `T59a` --- the theorem that makes the two hypotheses
                // interchangeable --- is proved *from* the second. Same
                // conclusion, different theorems.
                //
                // So a collision is reported only when the two proofs are
                // substantially the same text. That is a net, not a proof: two
                // spellings of one argument slip through, and only reading
                // catches those.
                if body.contains(first_name.as_str()) {
                    continue;
                }
                let normalize = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
                // Identical proof text is one proof written twice, and that is
                // decidable. Merely *similar* text is not: `inSpan_append_lo`
                // and `inSpan_append_hi` conclude the same thing by parallel
                // arguments about different hypotheses, and no threshold
                // separates that from a genuine copy without over-fitting to
                // whatever happens to sit in the tree today. So the gate fails
                // on the decidable case and reports the rest for review --- the
                // duplicates removed today were found exactly that way, by
                // reading a candidate list.
                if normalize(&body) != normalize(first_body) {
                    review.push(format!(
                        "  {name} in {module} and {first_name} in {first_module}"
                    ));
                    continue;
                }
                let where_ = if *first_module == module {
                    format!("`{first_name}` in the same module")
                } else {
                    format!("`{first_name}` in {first_module}")
                };
                return Err(Fail::from(format!(
                    "R4: `{name}` in {module} proves the same conclusion as {where_}; import it, or move it to a module both import --- never a second proof"
                )));
            } else {
                by_conclusion.insert(statement, (module.clone(), name, body));
            }
        }
    }
    if !review.is_empty() {
        println!(
            "audit-atlas-duplication: {} pair(s) share a conclusion by different proofs; not a failure, and not nothing --- read them:",
            review.len()
        );
        for line in &review {
            println!("{line}");
        }
    }
    println!(
        "audit-atlas-duplication: {counted} public statements across {} vendored modules, no proof written twice (R4)",
        files.len()
    );
    Ok(())
}

/// Each public declaration's name and the conclusion of its statement.
fn public_statements(text: &str) -> Vec<(String, String, String, bool, String)> {
    let mut out = Vec::new();
    let lines: Vec<&str> = text.lines().collect();
    let mut index = 0usize;
    while index < lines.len() {
        let mut line = lines[index].trim_start();
        while let Some(rest) = line.strip_prefix("@[") {
            match rest.find(']') {
                Some(end) => line = rest[end + 1..].trim_start(),
                None => break,
            }
        }
        let Some(rest) = line.strip_prefix("public ") else {
            index += 1;
            continue;
        };
        let Some((keyword, tail)) = ["theorem ", "def ", "abbrev "]
            .iter()
            .find_map(|keyword| rest.strip_prefix(keyword).map(|tail| (*keyword, tail)))
        else {
            index += 1;
            continue;
        };
        let is_theorem = keyword == "theorem ";
        let name: String = tail
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '\'' || *c == '.')
            .collect();
        // The statement runs to the proof, which may be several lines below.
        let mut statement = String::new();
        let mut cursor = index;
        while cursor < lines.len() && cursor < index + 24 {
            let piece = if cursor == index {
                &tail[name.len()..]
            } else {
                lines[cursor]
            };
            if let Some(cut) = piece.find(":=") {
                statement.push(' ');
                statement.push_str(&piece[..cut]);
                break;
            }
            statement.push(' ');
            statement.push_str(piece);
            if piece.trim_end().ends_with(":= by") || piece.trim_end().ends_with("by") {
                break;
            }
            cursor += 1;
        }
        // Compare conclusions, not whole statements. The same lemma written in
        // two modules rarely matches character for character --- one may bind
        // `{n : Nat}` explicitly where the other takes it from a section
        // variable --- and an exact match therefore misses exactly the
        // redundancy this gate exists to find.
        let normalized = conclusion_of(&statement);
        let signature = statement.split_whitespace().collect::<Vec<_>>().join(" ");
        // A slice of the proof, enough to see whether this declaration simply
        // applies an earlier one. Two labels may share a single proof --- the
        // document names one equation in two sections --- and a declaration
        // that delegates is not a second proof of anything.
        let mut body = String::new();
        for line in lines.iter().skip(cursor).take(6) {
            body.push(' ');
            body.push_str(line);
        }
        if !name.is_empty() && !normalized.is_empty() {
            out.push((name, signature, normalized, is_theorem, body));
        }
        index += 1;
    }
    out
}

/// R4: nothing is deferred. The markers are spelled in halves so this gate
/// can scan its own source; exempting the file would put a hole exactly
/// where a deferral parked in a gate would sit.
pub fn audit_deferral(root: &Path) -> Result<(), Fail> {
    let markers = [
        concat!("TO", "DO"),
        concat!("FIX", "ME"),
        concat!("XX", "X"),
        concat!("unimplemented", "!"),
        concat!("to", "do!"),
        concat!("for ", "now"),
        concat!("later ", "version"),
    ];
    let mut files = Vec::new();
    gather(
        root,
        &[
            "crates", "xtask", "language", "schemas", "features", "examples", "model", "tests",
            "lean",
        ],
        &[
            ".rs", ".toml", ".json", ".md", ".feature", ".lex.tex", ".lean", ".txt", ".sh",
        ],
        &mut files,
    );
    root_tooling(root, &mut files);
    // Executables under fixture toolchains carry no extension.
    for entry in walkdir::WalkDir::new(root.join("tests"))
        .follow_links(false)
        .into_iter()
        .flatten()
    {
        let path = entry.path();
        if entry.file_type().is_file()
            && path
                .components()
                .any(|part| part.as_os_str() == "toolchain")
        {
            files.push(path.to_path_buf());
        }
    }
    files.sort();
    files.dedup();
    let mut violations = Vec::new();
    let mut in_fence = false;
    for path in files {
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        let rel = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .display()
            .to_string();
        let is_markdown = rel.ends_with(".md");
        in_fence = false;
        for (index, line) in text.lines().enumerate() {
            if is_markdown && line.trim_start().starts_with("```") {
                in_fence = !in_fence;
                continue;
            }
            if is_markdown && in_fence {
                continue;
            }
            for marker in markers {
                if line.contains(marker) && (!is_markdown || outside_code_spans(line, marker)) {
                    violations.push(format!("{rel}:{}: {}", index + 1, line.trim()));
                }
            }
        }
    }
    let _ = in_fence;
    if !violations.is_empty() {
        return Err(format!(
            "R4: nothing is deferred. None of {} may appear outside a code span.\n\n{}",
            markers.join(", "),
            violations.join("\n")
        )
        .into());
    }
    println!("audit-deferral: nothing is deferred (R4)");
    Ok(())
}

/// Diagnostic-code-shaped literals that are deliberately unregistered:
/// negative sentinels a test hands to `explain` to prove an unknown code
/// is rejected. They may appear only in test and conformance sources.
const NEGATIVE_SENTINELS: [&str; 1] = ["LLX9999"];

/// Every `LL<letter><four digits>` token in `text`.
fn code_tokens(text: &str) -> Vec<String> {
    text.split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|token| {
            token.len() == 7
                && token.starts_with("LL")
                && token.as_bytes()[2].is_ascii_uppercase()
                && token.as_bytes()[3..].iter().all(u8::is_ascii_digit)
        })
        .map(str::to_owned)
        .collect()
}

fn is_test_source(relative: &str) -> bool {
    relative.starts_with("crates/conformance/")
        || relative.contains("/tests/")
        || relative.starts_with("xtask/")
}

/// R5, §26.1: every diagnostic code used in Rust, tests, fixtures, or
/// documentation is registered, and every registered code is emitted
/// somewhere in the shipped sources. Rust is scanned for every
/// code-shaped literal, not only `code!(` arguments, so a code cannot be
/// smuggled through a string; the declared negative sentinels are the only
/// unregistered tokens allowed, and only in test sources.
pub fn audit_errors(root: &Path, model: &repo_model::Model) -> Result<(), Fail> {
    let registered: BTreeSet<&str> = model
        .errors
        .error
        .iter()
        .map(|row| row.code.as_str())
        .collect();
    for sentinel in NEGATIVE_SENTINELS {
        if registered.contains(sentinel) {
            return Err(format!(
                "R5: the negative sentinel `{sentinel}` must not be a registered code"
            )
            .into());
        }
    }

    // Codes constructed in Rust through the checked macro, and every other
    // code-shaped token in Rust source.
    let mut constructed: BTreeSet<String> = BTreeSet::new();
    let mut rust_files = Vec::new();
    gather(root, &["crates", "xtask"], &[".rs"], &mut rust_files);
    for path in &rust_files {
        if path.extension().is_none_or(|extension| extension != "rs") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        let relative = path
            .strip_prefix(root)
            .unwrap_or(path)
            .to_string_lossy()
            .replace('\\', "/");
        let mut at = 0usize;
        while let Some(position) = text[at..].find("code!(\"") {
            let start = at + position + 7;
            if let Some(end) = text[start..].find('"') {
                constructed.insert(text[start..start + end].to_owned());
                at = start + end;
            } else {
                break;
            }
        }
        for (index, line) in text.lines().enumerate() {
            for token in code_tokens(line) {
                if registered.contains(token.as_str()) {
                    continue;
                }
                if NEGATIVE_SENTINELS.contains(&token.as_str()) {
                    if is_test_source(&relative) {
                        continue;
                    }
                    return Err(format!(
                        "R5: {relative}:{}: the negative sentinel `{token}` may appear only in test sources",
                        index + 1
                    )
                    .into());
                }
                return Err(format!(
                    "R5: {relative}:{}: `{token}` is not a registered diagnostic code (§26.1)",
                    index + 1
                )
                .into());
            }
        }
    }
    for code in &constructed {
        if !registered.contains(code.as_str()) {
            return Err(format!(
                "R5: `{code}` is constructed in Rust but not registered in model/errors.toml"
            )
            .into());
        }
    }
    let mut shipped_constructed: BTreeSet<String> = BTreeSet::new();
    let mut shipped_files = Vec::new();
    gather(root, &["crates/lexlean/src"], &[".rs"], &mut shipped_files);
    for path in &shipped_files {
        if path.extension().is_none_or(|extension| extension != "rs") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        let mut at = 0usize;
        while let Some(position) = text[at..].find("code!(\"") {
            let start = at + position + 7;
            if let Some(end) = text[start..].find('"') {
                shipped_constructed.insert(text[start..start + end].to_owned());
                at = start + end;
            } else {
                break;
            }
        }
    }
    for code in &registered {
        if !shipped_constructed.contains(*code as &str) {
            return Err(format!(
                "R5: `{code}` is registered but never constructed by the shipped crate; an unused registered code is a claim with nothing behind it (§26.1)"
            )
            .into());
        }
    }

    // Codes mentioned anywhere else must be registered too.
    let mut mention_files = Vec::new();
    gather(
        root,
        &["tests", "features", "examples", "model"],
        &[".toml", ".json", ".feature", ".md", ".txt"],
        &mut mention_files,
    );
    for path in mention_files {
        // SPEC.md is the normative source and states whole code *ranges*
        // (SPEC.md 26.2); range bounds are not claims this repository
        // makes, so the specification is not scanned.
        if path.file_name().is_some_and(|name| name == "SPEC.md") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        // A fenced block in VERIFICATION.md is quoted gate output, not a
        // claim this repository makes: a falsifiability record shows what
        // the gate printed when its defect was planted, and a planted
        // defect is by construction an unregistered code (§27.9, and the
        // same allowance §27.10 gives fenced code in the deferral audit).
        // Everything outside the fences is still scanned.
        let quoted_output = path
            .file_name()
            .is_some_and(|name| name == "VERIFICATION.md");
        let mut fenced = false;
        for line in text.lines() {
            if line.trim_start().starts_with("```") {
                fenced = !fenced;
                continue;
            }
            if quoted_output && fenced {
                continue;
            }
            for token in code_tokens(line) {
                if !registered.contains(token.as_str()) {
                    return Err(format!(
                        "R5: `{token}` in {} is not a registered diagnostic code",
                        path.display()
                    )
                    .into());
                }
            }
        }
    }
    println!(
        "audit-errors: {} registered codes, every one constructed by the shipped crate, no unsanctioned literal in Rust, fixtures, or documentation (R5)",
        registered.len()
    );
    Ok(())
}

/// R6, §8.4: only `lexlean` ships, and no shipped crate depends on a
/// `publish = false` repository crate.
pub fn audit_shipped(root: &Path) -> Result<(), Fail> {
    let mut shipped = Vec::new();
    for entry in std::fs::read_dir(root.join("crates"))? {
        let path = entry?.path();
        let manifest = path.join("Cargo.toml");
        let Ok(text) = std::fs::read_to_string(&manifest) else {
            continue;
        };
        if !text.lines().any(|line| line.trim() == "publish = false") {
            shipped.push((
                path.file_name()
                    .unwrap_or_default()
                    .to_string_lossy()
                    .to_string(),
                text,
            ));
        }
    }
    let names: Vec<&str> = shipped.iter().map(|(name, _)| name.as_str()).collect();
    if names != ["lexlean"] {
        return Err(
            format!("R6: exactly the lexlean crate ships; shipped set is {names:?}").into(),
        );
    }
    for (name, manifest) in &shipped {
        for forbidden in ["repo-model", "repo-conformance", "xtask"] {
            if manifest.contains(&format!("{forbidden} ="))
                || manifest.contains(&format!("{forbidden}.workspace"))
            {
                return Err(format!(
                    "R6: shipped crate `{name}` depends on repository-only `{forbidden}`"
                )
                .into());
            }
        }
    }
    // The shipped crate reaches the repository-root normative data through
    // in-crate links that `cargo package` dereferences (SPEC.md §7 layout,
    // §21.2 embedding, RP-12 packaging). Each link must resolve to exactly
    // the root path it stands for, so the package embeds byte-identical
    // data and no second copy can drift.
    for (link, target) in [
        ("crates/lexlean/language", "language"),
        ("crates/lexlean/schemas", "schemas"),
        ("crates/lexlean/tests/golden", "tests/golden"),
        ("crates/lexlean/model/errors.toml", "model/errors.toml"),
        ("crates/lexlean/LICENSE-APACHE", "LICENSE-APACHE"),
        ("crates/lexlean/LICENSE-MIT", "LICENSE-MIT"),
    ] {
        let link_path = root.join(link);
        let resolved = std::fs::canonicalize(&link_path).map_err(|error| {
            format!("R6: {link}: the shipped crate's normative link is missing: {error}")
        })?;
        let expected = std::fs::canonicalize(root.join(target))?;
        if resolved != expected {
            return Err(format!(
                "R6: {link} resolves to {} rather than {target}; the crate must embed the repository's own normative data",
                resolved.display()
            )
            .into());
        }
    }
    println!("audit-shipped: only lexlean ships, with no repository-only dependency, and its normative links resolve to the repository data (R6)");
    Ok(())
}

/// §27.10: generated documents and schemas are current. The document halves
/// are compared by `check_model`; this audit proves every committed schema
/// is canonical JSON with the expected identity.
pub fn audit_generated(root: &Path) -> Result<(), Fail> {
    let schema_dir = root.join("schemas");
    let mut count = 0usize;
    for entry in std::fs::read_dir(&schema_dir)? {
        let path = entry?.path();
        if path.extension().is_none_or(|extension| extension != "json") {
            continue;
        }
        count += 1;
        let bytes = std::fs::read(&path)?;
        let value: serde_json::Value = serde_json::from_slice(&bytes)
            .map_err(|error| format!("{}: {error}", path.display()))?;
        let canonical = serde_json::to_string(&sorted(value))?;
        let expected = format!("{canonical}\n");
        if bytes != expected.as_bytes() {
            return Err(format!(
                "R10: {} is not canonical JSON; regenerate the schema",
                path.display()
            )
            .into());
        }
        let name = path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();
        let identity = format!("https://github.com/afflom/lexlean/schemas/{name}");
        if !canonical.contains(&identity) {
            return Err(format!("{}: missing its $id `{identity}`", path.display()).into());
        }
    }
    if count != 9 {
        return Err(format!("§7 commits exactly 9 schemas, found {count}").into());
    }
    println!("audit-generated: {count} schemas canonical and identified");
    Ok(())
}

fn sorted(value: serde_json::Value) -> serde_json::Value {
    match value {
        serde_json::Value::Object(map) => {
            let mut ordered = serde_json::Map::new();
            let mut keys: Vec<String> = map.keys().cloned().collect();
            keys.sort();
            for key in keys {
                let inner = map.get(&key).cloned().unwrap_or(serde_json::Value::Null);
                ordered.insert(key, sorted(inner));
            }
            serde_json::Value::Object(ordered)
        }
        serde_json::Value::Array(items) => {
            serde_json::Value::Array(items.into_iter().map(sorted).collect())
        }
        other => other,
    }
}

/// The §13.10 required semantic token IDs, exactly as the specification
/// lists them (56 IDs). Preamble options, package names, environment names,
/// and titles the fixed backend emits are additional core rows justified by
/// §13.10's second sentence and are checked through the backend source
/// rather than this list.
const REQUIRED_TOKENS: [&str; 56] = [
    "documentclass",
    "usepackage",
    "newtheorem",
    "theoremstyle",
    "begin",
    "end",
    "center",
    "large",
    "section",
    "subsection",
    "label",
    "texttt",
    "operatorname",
    "mathbb",
    "mathrm",
    "proof",
    "definition",
    "theorem",
    "lemma",
    "corollary",
    "plus",
    "minus",
    "times",
    "cdot",
    "slash",
    "equals",
    "not-equals",
    "less",
    "less-equal",
    "greater",
    "greater-equal",
    "member",
    "not-member",
    "subset",
    "subset-equal",
    "union",
    "intersection",
    "forall",
    "exists",
    "exists-unique",
    "logical-and",
    "logical-or",
    "logical-not",
    "implies",
    "iff",
    "mapsto",
    "arrow",
    "left-arrow",
    "comma",
    "period",
    "colon",
    "semicolon",
    "left-paren",
    "right-paren",
    "left-bracket",
    "right-bracket",
];

/// Every string literal in `text` (Rust source, no raw strings needed): the
/// bytes between unescaped double quotes.
fn string_literals(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut chars = text.chars().peekable();
    let mut in_line_comment = false;
    let mut previous = '\0';
    while let Some(c) = chars.next() {
        if in_line_comment {
            if c == '\n' {
                in_line_comment = false;
            }
            previous = c;
            continue;
        }
        if c == '/' && chars.peek() == Some(&'/') {
            in_line_comment = true;
            previous = c;
            continue;
        }
        if c == '"' && previous != '\\' && previous != '\'' {
            let mut literal = String::new();
            let mut escaped = false;
            for inner in chars.by_ref() {
                if escaped {
                    literal.push(inner);
                    escaped = false;
                } else if inner == '\\' {
                    escaped = true;
                } else if inner == '"' {
                    break;
                } else {
                    literal.push(inner);
                }
            }
            out.push(literal);
            previous = '"';
            continue;
        }
        previous = c;
    }
    out
}

/// The literals passed directly to `sink.tok("...")`, `.tok("...")`, or
/// `tok!("...")`-style calls: the certain backend references.
fn direct_tok_literals(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut at = 0usize;
    while let Some(position) = text[at..].find(".tok(\"") {
        let start = at + position + ".tok(\"".len();
        if let Some(end) = text[start..].find('"') {
            out.insert(text[start..start + end].to_owned());
            at = start + end;
        } else {
            break;
        }
    }
    out
}

/// §13.10, §27.10: the renderer-token registry equals the minimal transitive
/// closure of tokens referenced by the fixed backend (its preamble and
/// deterministic constructs, read from the backend source) and every shipped
/// LRE, and carries every required semantic ID.
///
/// The backend's references are derived from `crates/lexlean/src/backend`:
/// every literal passed directly to `sink.tok("...")` is a certain
/// reference; `language/bootstrap.toml [backend].tokens` is the backend's
/// declared reference list, and the audit requires the two to agree in both
/// directions — every direct literal is declared, and every declared token
/// occurs as a string literal in the backend source (tokens selected through
/// a variable, such as environment names, are still literals there).
pub fn audit_language_closure(root: &Path) -> Result<(), Fail> {
    let registry_text = std::fs::read_to_string(root.join("language/renderer-tokens.toml"))?;
    let registry: toml::Value = registry_text.parse()?;
    let registry_ids: BTreeSet<String> = registry
        .get("token")
        .and_then(|tokens| tokens.as_array())
        .map(|tokens| {
            tokens
                .iter()
                .filter_map(|token| token.get("id").and_then(|id| id.as_str()))
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default();

    let bootstrap_text = std::fs::read_to_string(root.join("language/bootstrap.toml"))?;
    let bootstrap: toml::Value = bootstrap_text.parse()?;
    let declared: BTreeSet<String> = bootstrap
        .get("backend")
        .and_then(|backend| backend.get("tokens"))
        .and_then(|tokens| tokens.as_array())
        .map(|tokens| {
            tokens
                .iter()
                .filter_map(|token| token.as_str())
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default();

    // The backend source: direct `sink.tok("...")` literals and every string
    // literal (for variable-selected tokens).
    let mut backend_files = Vec::new();
    gather(
        root,
        &["crates/lexlean/src/backend"],
        &[".rs"],
        &mut backend_files,
    );
    let mut direct: BTreeSet<String> = BTreeSet::new();
    let mut literals: BTreeSet<String> = BTreeSet::new();
    for path in backend_files
        .iter()
        .filter(|path| path.extension().is_some_and(|extension| extension == "rs"))
    {
        let text = std::fs::read_to_string(path)?;
        direct.extend(direct_tok_literals(&text));
        literals.extend(string_literals(&text));
    }
    if direct.is_empty() {
        return Err("R8: the backend source contains no `sink.tok(\"...\")` reference; the audit is not armed".into());
    }
    let undeclared: Vec<&String> = direct.difference(&declared).collect();
    if !undeclared.is_empty() {
        return Err(format!(
            "R8: the backend emits tokens that language/bootstrap.toml [backend].tokens does not declare: {undeclared:?}"
        )
        .into());
    }
    let stale: Vec<&String> = declared
        .iter()
        .filter(|token| !literals.contains(*token))
        .collect();
    if !stale.is_empty() {
        return Err(format!(
            "R8: language/bootstrap.toml [backend].tokens declares tokens the backend source never names: {stale:?}"
        )
        .into());
    }

    let mut referenced: BTreeSet<String> = declared;
    for entry in walkdir::WalkDir::new(root.join("language"))
        .into_iter()
        .flatten()
    {
        if !entry.file_type().is_file()
            || entry
                .path()
                .extension()
                .is_none_or(|extension| extension != "toml")
        {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(entry.path()) else {
            continue;
        };
        let mut at = 0usize;
        while let Some(position) = text[at..].find("(token ") {
            let start = at + position + 7;
            let end = text[start..]
                .find(')')
                .map(|offset| start + offset)
                .unwrap_or(text.len());
            referenced.insert(text[start..end].trim().to_owned());
            at = end;
        }
    }

    for required in REQUIRED_TOKENS {
        if !registry_ids.contains(required) {
            return Err(format!("R8: required renderer token `{required}` is missing").into());
        }
    }
    let missing: Vec<&String> = referenced.difference(&registry_ids).collect();
    if !missing.is_empty() {
        return Err(format!("R8: referenced tokens missing from the registry: {missing:?}").into());
    }
    let unused: Vec<&String> = registry_ids.difference(&referenced).collect();
    if !unused.is_empty() {
        return Err(format!(
            "R8: unused registry rows fail the language audit (§13.10): {unused:?}"
        )
        .into());
    }
    println!(
        "audit-language-closure: {} tokens, registry equals the referenced closure ({} backend, {} required) (R8)",
        registry_ids.len(),
        direct.len(),
        REQUIRED_TOKENS.len()
    );
    Ok(())
}

/// §8.1, §27.10: the shipped crate forbids unsafe Rust and the prohibition
/// is active in every shipped source file.
pub fn audit_no_unsafe(root: &Path) -> Result<(), Fail> {
    let lib = std::fs::read_to_string(root.join("crates/lexlean/src/lib.rs"))?;
    let marker = concat!("#![forbid(un", "safe_code)]");
    if !lib.contains(marker) {
        return Err("R6: crates/lexlean/src/lib.rs must carry the crate-level prohibition".into());
    }
    let needle = concat!("un", "safe ");
    let mut files = Vec::new();
    gather(root, &["crates/lexlean/src"], &[".rs"], &mut files);
    for path in files {
        if path.extension().is_none_or(|extension| extension != "rs") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        for (index, line) in text.lines().enumerate() {
            let stripped = line.split("//").next().unwrap_or("");
            if stripped.contains(needle) && !stripped.contains("forbid") {
                return Err(format!(
                    "R6: {}:{} contains an unguarded keyword the shipped crate forbids",
                    path.display(),
                    index + 1
                )
                .into());
            }
        }
    }
    println!("audit-no-unsafe: the prohibition is active (RP-09)");
    Ok(())
}

/// The conclusion of a statement: what follows its last binder-closing `:` at
/// bracket depth zero, whitespace-normalized. Binders differ freely between two
/// spellings of one lemma; the conclusion does not.
fn conclusion_of(statement: &str) -> String {
    let bytes: Vec<char> = statement.chars().collect();
    let mut depth = 0i32;
    let mut last = None;
    let mut index = 0usize;
    while index < bytes.len() {
        match bytes[index] {
            '(' | '[' | '{' | '\u{27e8}' => depth += 1,
            ')' | ']' | '}' | '\u{27e9}' => depth -= 1,
            // `::` is a qualified-name separator, never a binder close.
            ':' if depth == 0
                && bytes.get(index + 1) != Some(&':')
                && bytes.get(index.wrapping_sub(1)) != Some(&':') =>
            {
                last = Some(index);
            }
            _ => {}
        }
        index += 1;
    }
    let tail = match last {
        Some(at) => {
            &statement[statement
                .char_indices()
                .nth(at + 1)
                .map_or(statement.len(), |(i, _)| i)..]
        }
        None => statement,
    };
    tail.split_whitespace().collect::<Vec<&str>>().join(" ")
}
