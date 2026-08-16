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
use crate::lexicon::package::{load_package, LexiconPackage, PackageRef};

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

/// The fixed structural sets (§15.2, §12.4).
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
        if token.authority != "lexlean.core" {
            return Err(Diagnostic::new(
                code!("LLI9001"),
                format!("phase language-load: token `{}` authority drift", token.id),
            ));
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
pub fn load_builtin_package(row: &BuiltinPackage) -> Result<LexiconPackage, Vec<Diagnostic>> {
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
    load_package(&format!("builtin:{}", row.id), &files, Some(&expected))
}
