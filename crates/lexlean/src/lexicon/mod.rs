//! The closed lexicon: language bootstrap data, the renderer-token registry,
//! packages, entries, LSE, LRE, and resolution (SPEC.md §12.3, §13).

pub mod entry;
pub mod lre;
pub mod lse;
pub mod package;
pub mod resolve;

use std::collections::BTreeMap;

use serde::Deserialize;

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::lexicon::package::{load_package, LexiconPackage, LoadContext, PackageRef};

/// The parsed `language/bootstrap.toml`: the fixed structural sets and the
/// renderer tokens the fixed backend references (§12.4, §15.2, §13.10).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Bootstrap {
    /// The schema tag.
    pub spec: String,
    /// The language identifier.
    pub language: String,
    /// The embedded builtin packages, in load order.
    #[serde(rename = "builtin_package")]
    pub builtin_packages: Vec<BuiltinPackage>,
    /// The structural sets.
    pub structural: StructuralSets,
    /// The backend token references.
    pub backend: BackendTokens,
}

/// One embedded builtin package row.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BuiltinPackage {
    /// The package ID.
    pub id: String,
    /// The exact version.
    pub version: String,
    /// The path under `language/`.
    pub path: String,
    /// Is this package part of the language every document is written in,
    /// rather than one a project selects?
    ///
    /// An unconditional package is locked into every project and visible in
    /// every module without a `\useglossary` row. Both properties are read
    /// from here rather than spelled out at the two call sites, because a
    /// package that is locked but not visible --- or visible but not locked ---
    /// is a state no row can express and therefore one no change can reach by
    /// halves.
    #[serde(default)]
    pub unconditional: bool,
}

impl Bootstrap {
    /// The packages every project locks and every module sees.
    #[must_use]
    pub fn unconditional_packages(&self) -> Vec<String> {
        self.builtin_packages
            .iter()
            .filter(|row| row.unconditional)
            .map(|row| row.id.clone())
            .collect()
    }
}

/// The fixed structural sets (§15.2, §12.4). These are the single source of
/// truth the compiler consults at runtime: the scanner-side forbidden-control
/// check, entry-form validation, and the structural grammar's control and
/// environment membership tests all read these lists.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StructuralSets {
    /// The complete structural control set.
    pub controls: Vec<String>,
    /// The complete environment-name set.
    pub environments: Vec<String>,
    /// The always-forbidden TeX controls.
    pub forbidden_controls: Vec<String>,
}

impl StructuralSets {
    /// Is `control` (with its backslash) a §15.2 structural control?
    #[must_use]
    pub fn is_control(&self, control: &str) -> bool {
        self.controls.iter().any(|c| c == control)
    }

    /// Is `name` a §15.2 environment name?
    #[must_use]
    pub fn is_environment(&self, name: &str) -> bool {
        self.environments.iter().any(|e| e == name)
    }

    /// Is `control` (with its backslash) always forbidden (§12.4)?
    #[must_use]
    pub fn is_forbidden_control(&self, control: &str) -> bool {
        self.forbidden_controls.iter().any(|c| c == control)
    }
}

/// The renderer tokens the fixed backend emits itself.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BackendTokens {
    /// Token IDs referenced by the preamble and deterministic constructs.
    pub tokens: Vec<String>,
}

/// One renderer-token registry row (§13.10).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RendererToken {
    /// The token ID.
    pub id: String,
    /// The exact emitted UTF-8 bytes.
    pub bytes: String,
    /// The channel: `text`, `math`, or `both`.
    pub channel: String,
    /// Argument arity.
    pub arity: u32,
    /// Whether emission requires a following brace group.
    pub grouping: bool,
    /// The source package authority, always core.
    pub authority: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawTokenRegistry {
    spec: String,
    #[serde(rename = "token")]
    tokens: Vec<RendererToken>,
}

/// The parsed renderer-token registry.
#[derive(Debug, Clone)]
pub struct TokenRegistry {
    /// Rows by token ID.
    pub tokens: BTreeMap<String, RendererToken>,
}

impl TokenRegistry {
    /// Look up a token.
    #[must_use]
    pub fn get(&self, id: &str) -> Option<&RendererToken> {
        self.tokens.get(id)
    }
}

fn embedded_text(path: &str) -> Result<&'static str, Diagnostic> {
    crate::embedded::FILES
        .iter()
        .find(|(candidate, _)| *candidate == path)
        .and_then(|(_, bytes)| std::str::from_utf8(bytes).ok())
        .ok_or_else(|| {
            Diagnostic::new(
                code!("LLI9001"),
                format!("phase language-load: embedded `{path}` is missing or not UTF-8"),
            )
        })
}

/// Load the embedded bootstrap data.
pub fn load_bootstrap() -> Result<Bootstrap, Diagnostic> {
    let text = embedded_text("language/bootstrap.toml")?;
    let bootstrap: Bootstrap = toml::from_str(text).map_err(|error| {
        Diagnostic::new(
            code!("LLI9001"),
            format!("phase language-load: invalid bootstrap data: {error}"),
        )
    })?;
    if bootstrap.spec != "lexlean/bootstrap/1" || bootstrap.language != crate::LANGUAGE_VERSION {
        return Err(Diagnostic::new(
            code!("LLI9001"),
            "phase language-load: bootstrap schema drift",
        ));
    }
    // The structural sets are exact and closed: every row is a control
    // (backslash then ASCII letters or one ASCII nonletter) or an ASCII
    // environment word, and no row repeats.
    fn is_control_row(text: &str) -> bool {
        let rest = text.strip_prefix('\\').unwrap_or("");
        !rest.is_empty()
            && (rest.bytes().all(|b| b.is_ascii_alphabetic())
                || (rest.len() == 1
                    && rest.is_ascii()
                    && !rest.as_bytes()[0].is_ascii_alphabetic()))
    }
    fn is_environment_row(text: &str) -> bool {
        !text.is_empty() && text.bytes().all(|b| b.is_ascii_lowercase())
    }
    type RowCheck = fn(&str) -> bool;
    let sets: [(&str, &Vec<String>, RowCheck); 3] = [
        ("controls", &bootstrap.structural.controls, is_control_row),
        (
            "forbidden_controls",
            &bootstrap.structural.forbidden_controls,
            is_control_row,
        ),
        (
            "environments",
            &bootstrap.structural.environments,
            is_environment_row,
        ),
    ];
    for (what, rows, valid) in sets {
        let unique: std::collections::BTreeSet<&String> = rows.iter().collect();
        if unique.len() != rows.len() || rows.iter().any(|row| !valid(row)) {
            return Err(Diagnostic::new(
                code!("LLI9001"),
                format!("phase language-load: bootstrap structural.{what} is not an exact set"),
            ));
        }
    }
    Ok(bootstrap)
}

/// Load the embedded renderer-token registry.
pub fn load_token_registry() -> Result<TokenRegistry, Diagnostic> {
    let text = embedded_text("language/renderer-tokens.toml")?;
    let raw: RawTokenRegistry = toml::from_str(text).map_err(|error| {
        Diagnostic::new(
            code!("LLI9001"),
            format!("phase language-load: invalid renderer-token registry: {error}"),
        )
    })?;
    if raw.spec != "lexlean/renderer-tokens/1" {
        return Err(Diagnostic::new(
            code!("LLI9001"),
            "phase language-load: renderer-token schema drift",
        ));
    }
    let mut tokens = BTreeMap::new();
    for token in raw.tokens {
        let drift = |reason: &str| {
            Diagnostic::new(
                code!("LLI9001"),
                format!("phase language-load: token `{}` {reason}", token.id),
            )
        };
        if token.authority != "lexlean.core" {
            return Err(drift("authority drift"));
        }
        if !crate::lexicon::lre::is_token_id(&token.id) {
            return Err(drift("has an invalid ID"));
        }
        if !matches!(token.channel.as_str(), "text" | "math" | "both") {
            return Err(drift("has an invalid channel"));
        }
        // Emitted bytes are exact and non-empty, contain no line break, no
        // comment character, and no NUL; a token that takes arguments is a
        // control word or one of TeX's two script characters (`_`, `^`),
        // and grouping is exactly the arity > 0 case (the backend emits
        // `\\control{...}` or `_{...}` for each argument).
        let is_control_word =
            token.bytes.strip_prefix('\\').is_some_and(|rest| {
                !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_alphabetic())
            }) || (token.arity == 1 && matches!(token.bytes.as_str(), "_" | "^"));
        if token.bytes.is_empty()
            || token
                .bytes
                .chars()
                .any(|c| c == '\n' || c == '\r' || c == '%' || c == '\0')
        {
            return Err(drift("emits invalid bytes"));
        }
        if token.grouping != (token.arity > 0) {
            return Err(drift("grouping must hold exactly when arity > 0"));
        }
        if token.arity > 0 && !is_control_word {
            return Err(drift("declares arguments without being a control word"));
        }
        if tokens.insert(token.id.clone(), token).is_some() {
            return Err(Diagnostic::new(
                code!("LLI9001"),
                "phase language-load: duplicate renderer token",
            ));
        }
    }
    Ok(TokenRegistry { tokens })
}

/// Load one embedded builtin package by its bootstrap row.
pub fn load_builtin_package(
    row: &BuiltinPackage,
    ctx: &LoadContext<'_>,
) -> Result<LexiconPackage, Vec<Diagnostic>> {
    let prefix = format!("language/{}/", row.path);
    let mut files: Vec<(String, Vec<u8>)> = crate::embedded::FILES
        .iter()
        .filter_map(|(path, bytes)| {
            path.strip_prefix(&prefix)
                .map(|relative| (relative.to_owned(), (*bytes).to_vec()))
        })
        .filter(|(relative, _)| relative == "lexicon.toml" || relative.starts_with("entries/"))
        .collect();
    files.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    let expected = PackageRef {
        package: row.id.clone(),
        version: row.version.clone(),
    };
    load_package(&format!("builtin:{}", row.id), &files, Some(&expected), ctx)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexicon::entry::{is_lean_name, Denotation};
    use crate::lexicon::resolve::Closure;

    fn builtins() -> (Bootstrap, Vec<LexiconPackage>) {
        let bootstrap = load_bootstrap().expect("bootstrap loads");
        let ctx = LoadContext {
            forbidden_controls: &bootstrap.structural.forbidden_controls,
            max_scope_depth: 1024,
        };
        let packages = bootstrap
            .builtin_packages
            .iter()
            .map(|row| load_builtin_package(row, &ctx).expect("builtin package loads"))
            .collect();
        (bootstrap, packages)
    }

    #[test]
    fn embedded_language_data_loads_and_closes() {
        let (bootstrap, packages) = builtins();
        assert_eq!(bootstrap.builtin_packages.len(), 4);
        assert!(bootstrap.structural.is_control("\\begin"));
        assert!(!bootstrap.structural.is_control("\\def"));
        assert!(bootstrap.structural.is_forbidden_control("\\def"));
        assert!(bootstrap.structural.is_environment("theorem"));
        let registry = load_token_registry().expect("registry loads");
        assert!(registry.get("logical-and").is_some());
        Closure::build(packages, registry, bootstrap, 128).expect("the builtin closure validates");
    }

    #[test]
    fn token_lattice_counts_each_edge_once() {
        use crate::lexicon::entry::Channel;
        use crate::lexicon::resolve::TokenLattice;
        let (bootstrap, packages) = builtins();
        let registry = load_token_registry().expect("registry loads");
        let closure = Closure::build(packages, registry, bootstrap, 128).expect("closure");
        let atoms = crate::source::scan::scan("m", "natural number list", 100).expect("scans");
        let visible = closure.visible_set(&["lexlean.std.nat".to_owned()]);
        let mut lattice = TokenLattice::new(100);
        let first = lattice
            .edges_at(&closure, &atoms, &visible, 0, Channel::Text)
            .expect("edges")
            .len();
        assert!(
            first >= 2,
            "`natural number` and `natural number list` both start here"
        );
        let counted = lattice.edge_count();
        for _ in 0..10 {
            lattice
                .edges_at(&closure, &atoms, &visible, 0, Channel::Text)
                .expect("memoized");
        }
        assert_eq!(lattice.edge_count(), counted, "revisits are free");
        let mut tight = TokenLattice::new(1);
        let limited = tight
            .edges_at(&closure, &atoms, &visible, 0, Channel::Text)
            .expect_err("limited");
        assert_eq!(limited.code.as_str(), "LLS8002");
        assert!(
            limited.message.contains("configured 1") && limited.message.contains("observed"),
            "the limit diagnostic names the configured value and the observation: {}",
            limited.message
        );
    }

    /// Every builtin Lean denotation is spelled per the conservative grammar
    /// and names a constant that elaborates under Lean 4.32.1 at the entry's
    /// signature (probed with `example : <signature> := <name>`; the list
    /// below is that probe's accepted set).
    #[test]
    fn builtin_lean_names_are_conservative_and_known() {
        const KNOWN: [&str; 31] = [
            "And.intro",
            "Exists.intro",
            "Iff.intro",
            "Int",
            "Int.add",
            "Int.ediv",
            "Int.emod",
            "Int.le",
            "Int.lt",
            "Int.mul",
            "Int.neg",
            "Int.sign",
            "Int.sub",
            "List",
            "List.Mem",
            "List.Subset",
            "List.append",
            "List.removeAll",
            "Nat",
            "Nat.add",
            "Nat.div",
            "Nat.le",
            "Nat.lt",
            "Nat.mul",
            "Nat.sub",
            "Nat.succ",
            "Nat.zero",
            "Ne",
            "Or.inl",
            "Or.inr",
            "Prod",
        ];
        let (_, packages) = builtins();
        let mut seen = 0usize;
        for package in &packages {
            for entry in package.entries.values() {
                if let Denotation::Lean { module, name } = &entry.denotation {
                    assert!(is_lean_name(module) && is_lean_name(name), "{name}");
                    // Core and standard packages denote Lean's own constants,
                    // and the list above is the probe's accepted set. The
                    // Atlas package names project into the native Atlas
                    // declaration graph. This crate embeds the frozen package,
                    // while the repository audit reads the native source and
                    // checks that every projected declaration exists.
                    if let Some(rest) = module.strip_prefix("UorAtlas") {
                        assert!(
                            rest.is_empty() || rest.starts_with('.'),
                            "`{module}` is not an Atlas module"
                        );
                        assert!(
                            name.starts_with("UorAtlas."),
                            "`{name}` is not in the native Atlas namespace"
                        );
                    } else {
                        assert!(
                            KNOWN.contains(&name.as_str()),
                            "`{name}` is not in the probed Lean 4.32.1 name set"
                        );
                    }
                    seen += 1;
                }
                if let Some(eliminator) = &entry.eliminator {
                    assert!(is_lean_name(&eliminator.cases_lean_name));
                    assert!(is_lean_name(&eliminator.induction_lean_name));
                    for constructor in &eliminator.constructors {
                        assert!(is_lean_name(&constructor.lean_name));
                    }
                }
            }
        }
        assert!(
            seen >= 20,
            "the builtin packages carry Lean denotations ({seen})"
        );
    }
}
