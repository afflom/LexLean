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
    let sets: [(&str, &Vec<String>, fn(&str) -> bool); 3] = [
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
        // control word, and grouping is exactly the arity > 0 case (the
        // backend emits `\\control{...}` for each argument).
        let is_control_word = token
            .bytes
            .strip_prefix('\\')
            .is_some_and(|rest| !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_alphabetic()));
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
