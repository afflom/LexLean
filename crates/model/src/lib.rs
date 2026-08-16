//! Typed registries parsed from `model/*.toml`.
//!
//! The model is authored once and has exactly one source (R1): the conformance
//! ID register, the claim ledger, and the authorities this repository cites.
//! `CONFORMANCE.md` is generated from it by [`codegen`], so a claim cannot exist
//! in the documentation without a ledger row, or in the ledger without appearing
//! in the documentation.
//!
//! This crate is build-time and CI infrastructure. It is not a dependency of
//! any shipped crate, and it may use `std`.

#![deny(missing_docs)]

pub mod codegen;
pub mod registry;
pub mod release;

pub use registry::{Authorities, AuthorityRow, Claim, ErrorRow, Errors, IdRow, Ids, Ledger, Level};

use std::path::{Path, PathBuf};

/// Everything `model/*.toml` says, parsed and cross-checked.
#[derive(Debug, Clone)]
pub struct Model {
    /// `model/ledger.toml`: one row per claim, at exactly one honesty level.
    pub ledger: Ledger,
    /// `model/ids.toml`: the conformance ID register.
    pub ids: Ids,
    /// `model/authorities.toml`: what this repository cites rather than proves.
    pub authorities: Authorities,
    /// `model/errors.toml`: the closed public diagnostic registry (R1, R5).
    pub errors: Errors,
}

/// A failure to load or to cross-check the model.
#[derive(Debug)]
pub enum ModelError {
    /// A model file could not be read.
    Io(PathBuf, std::io::Error),
    /// A model file could not be parsed.
    Parse(PathBuf, toml::de::Error),
    /// The model disagrees with itself, or with a derivation (R1).
    Inconsistent(String),
}

impl std::fmt::Display for ModelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(p, e) => write!(f, "reading {}: {e}", p.display()),
            Self::Parse(p, e) => write!(f, "parsing {}: {e}", p.display()),
            Self::Inconsistent(m) => write!(f, "model is inconsistent: {m}"),
        }
    }
}

impl std::error::Error for ModelError {}

impl Model {
    /// Load every model file from a `model/` directory.
    pub fn load(dir: &Path) -> Result<Self, ModelError> {
        Ok(Self {
            ledger: read(dir, "ledger.toml")?,
            ids: read(dir, "ids.toml")?,
            authorities: read(dir, "authorities.toml")?,
            errors: read(dir, "errors.toml")?,
        })
    }

    /// Load the model from the repository root, resolved from this crate's
    /// manifest directory so that it works from any working directory.
    pub fn load_from_repo_root() -> Result<Self, ModelError> {
        Self::load(&repo_root().join("model"))
    }

    /// Cross-check the model against itself: every ID well formed, every claim
    /// well formed for its level, and every `some-true` claim bound to an
    /// authority that exists (R1, R2, §27.5 step 2).
    pub fn check(&self) -> Result<(), ModelError> {
        self.ledger.check()?;
        self.check_ids()?;
        self.check_authorities()?;
        self.errors.check()?;
        Ok(())
    }

    /// §27.5: every registered ID is well formed and, per §27.3, at level
    /// `build`; the ID shape is `<two upper-case letters>-<two digits>`
    /// (§27.8 derives the test name from it).
    fn check_ids(&self) -> Result<(), ModelError> {
        let bad = |m: String| ModelError::Inconsistent(m);
        let mut seen: Vec<&str> = Vec::new();
        for row in &self.ids.id {
            if seen.contains(&row.id.as_str()) {
                return Err(bad(format!("{}: registered twice", row.id)));
            }
            seen.push(&row.id);

            if row.statement.trim().is_empty() {
                return Err(bad(format!(
                    "{}: an untagged claim does not ship (R2)",
                    row.id
                )));
            }
            if row.suite.trim().is_empty() {
                return Err(bad(format!(
                    "{}: every ID names the Gherkin suite its scenario lives in (R3)",
                    row.id
                )));
            }
            if row.level != Level::Build {
                return Err(bad(format!(
                    "{}: every LexLean capability ID is level `build` (§27.3), found `{}`",
                    row.id,
                    row.level.as_str()
                )));
            }
            let bytes = row.id.as_bytes();
            let shaped = bytes.len() == 5
                && bytes[0].is_ascii_uppercase()
                && bytes[1].is_ascii_uppercase()
                && bytes[2] == b'-'
                && bytes[3].is_ascii_digit()
                && bytes[4].is_ascii_digit();
            if !shaped {
                return Err(bad(format!(
                    "{}: a conformance ID is two upper-case letters, a hyphen, and two digits (§27.8)",
                    row.id
                )));
            }
        }
        if self.ids.spec != "lexlean/ids/1" {
            return Err(bad(format!("ids.toml has spec `{}`", self.ids.spec)));
        }
        if self.ledger.spec != "lexlean/ledger/1" {
            return Err(bad(format!("ledger.toml has spec `{}`", self.ledger.spec)));
        }
        if self.authorities.spec != "lexlean/authorities/1" {
            return Err(bad(format!(
                "authorities.toml has spec `{}`",
                self.authorities.spec
            )));
        }
        Ok(())
    }

    /// §27.4: every `some-true` claim has a row in `model/authorities.toml`
    /// with a citation, and every authority names IDs that exist.
    fn check_authorities(&self) -> Result<(), ModelError> {
        let bad = |m: String| ModelError::Inconsistent(m);
        for a in &self.authorities.authority {
            if a.citation.trim().is_empty() {
                return Err(bad(format!("{}: an authority with no citation", a.id)));
            }
            if a.checksum == "none" && a.checksum_reason.trim().is_empty() {
                return Err(bad(format!(
                    "{}: no checksum and no reason. A missing checksum must be a stated \
                     fact, not an omission (R6)",
                    a.id
                )));
            }
            for id in &a.realized_by {
                if self.ids.get(id).is_none() {
                    return Err(bad(format!("{}: realized_by names unknown ID {id}", a.id)));
                }
            }
        }
        // Every some-true claim in the ledger names a known authority.
        for c in &self.ledger.claim {
            if c.level != Level::SomeTrue {
                continue;
            }
            let Some(name) = &c.authority else {
                return Err(bad(format!(
                    "{}: a some-true claim must name an authority",
                    c.id
                )));
            };
            if !self.authorities.authority.iter().any(|a| &a.id == name) {
                return Err(bad(format!(
                    "{}: cites {name}, which has no row in model/authorities.toml (§27.4)",
                    c.id
                )));
            }
        }
        Ok(())
    }
}

fn read<T: serde::de::DeserializeOwned>(dir: &Path, name: &str) -> Result<T, ModelError> {
    let path = dir.join(name);
    let text = std::fs::read_to_string(&path).map_err(|e| ModelError::Io(path.clone(), e))?;
    toml::from_str(&text).map_err(|e| ModelError::Parse(path, e))
}

/// The repository root, resolved from this crate's manifest directory.
pub fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("crates/model is two levels below the repository root")
        .to_path_buf()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// R1: the committed model is self-consistent.
    #[test]
    fn the_committed_model_is_consistent() {
        let model = Model::load_from_repo_root().expect("model loads");
        model.check().expect("model checks");
        assert!(!model.ids.id.is_empty(), "the register is populated");
        assert!(
            model.ids.id.iter().all(|row| row.level == Level::Build),
            "every LexLean ID is `build` (§27.3)"
        );
    }

    /// §27.4: every `some-true` claim cites an authority that exists.
    #[test]
    fn every_some_true_claim_cites_an_authority() {
        let model = Model::load_from_repo_root().expect("model loads");
        for c in &model.ledger.claim {
            if c.level == Level::SomeTrue {
                let name = c
                    .authority
                    .as_ref()
                    .expect("a some-true claim names its authority");
                assert!(
                    model.authorities.authority.iter().any(|a| &a.id == name),
                    "{name}"
                );
            }
        }
    }

    /// §27.5 step 1: every model file is parsed with unknown-field
    /// rejection, at the top level and inside every row.
    #[test]
    fn unknown_fields_are_rejected_in_every_model_file() {
        let dir = repo_root().join("model");
        let cases: [(&str, &[&str]); 4] = [
            ("ids.toml", &["spec = \"lexlean/ids/1\"", "id = \"RP-01\""]),
            (
                "ledger.toml",
                &["spec = \"lexlean/ledger/1\"", "level = \"some-true\""],
            ),
            (
                "authorities.toml",
                &["spec = \"lexlean/authorities/1\"", "checksum = \"none\""],
            ),
            (
                "errors.toml",
                &["spec = \"lexlean/errors/1\"", "class = \"language\""],
            ),
        ];
        for (file, anchors) in cases {
            let text = std::fs::read_to_string(dir.join(file)).expect("model file");
            for anchor in anchors {
                assert!(text.contains(anchor), "{file}: anchor {anchor}");
                let planted = text.replacen(anchor, &format!("{anchor}\nsurprise = 1"), 1);
                let outcome: Result<toml::Value, _> = toml::from_str(&planted);
                assert!(outcome.is_ok(), "the planted TOML itself parses");
                let typed = match file {
                    "ids.toml" => toml::from_str::<Ids>(&planted).map(|_| ()),
                    "ledger.toml" => toml::from_str::<Ledger>(&planted).map(|_| ()),
                    "authorities.toml" => toml::from_str::<Authorities>(&planted).map(|_| ()),
                    _ => toml::from_str::<Errors>(&planted).map(|_| ()),
                };
                let error = typed.expect_err("an unknown field is rejected");
                assert!(
                    error.to_string().contains("unknown field"),
                    "{file}: {error}"
                );
            }
        }
    }
}
