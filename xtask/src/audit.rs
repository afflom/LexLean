//! The repository audits (SPEC.md §27.10). Crude on purpose: each reads the
//! source, finds the defect, and fails naming the rule it enforces.

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
        ],
        &[
            ".rs", ".toml", ".json", ".md", ".feature", ".lex.tex", ".lean", ".txt",
        ],
        &mut files,
    );
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

/// R5, §26.1: every diagnostic code used in Rust, tests, fixtures, or
/// documentation is registered, and every registered code is emitted
/// somewhere in the shipped sources.
pub fn audit_errors(root: &Path, model: &repo_model::Model) -> Result<(), Fail> {
    let registered: BTreeSet<&str> = model
        .errors
        .error
        .iter()
        .map(|row| row.code.as_str())
        .collect();

    // Codes constructed in Rust through the checked macro.
    let mut constructed: BTreeSet<String> = BTreeSet::new();
    let mut rust_files = Vec::new();
    gather(root, &["crates", "xtask"], &[".rs"], &mut rust_files);
    for path in &rust_files {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
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
    }
    for code in &constructed {
        if !registered.contains(code.as_str()) {
            return Err(format!(
                "R5: `{code}` is constructed in Rust but not registered in model/errors.toml"
            )
            .into());
        }
    }
    for code in &registered {
        if !constructed.contains(*code as &str) {
            return Err(format!(
                "R5: `{code}` is registered but never constructed; an unused registered code is a claim with nothing behind it (§26.1)"
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
        // (`LLC0001`-`LLC0999`, SPEC.md 26.2); range bounds are not claims
        // this repository makes, so the specification is not scanned.
        if path.file_name().is_some_and(|name| name == "SPEC.md") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        for token in text.split(|c: char| !c.is_ascii_alphanumeric()) {
            if token.len() == 7
                && token.starts_with("LL")
                && token.as_bytes()[2].is_ascii_uppercase()
                && token.as_bytes()[3..].iter().all(u8::is_ascii_digit)
                && !registered.contains(token)
            {
                return Err(format!(
                    "R5: `{token}` in {} is not a registered diagnostic code",
                    path.display()
                )
                .into());
            }
        }
    }
    println!(
        "audit-errors: {} registered codes, every one constructed and none unsanctioned (R5)",
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
    println!("audit-shipped: only lexlean ships, with no repository-only dependency (R6)");
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
