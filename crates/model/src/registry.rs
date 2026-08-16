//! The typed shape of `model/*.toml`.
//!
//! Nothing here interprets the model; [`crate::Model::check`] does that. These
//! types exist so that a malformed model is a parse error rather than a
//! silently wrong constant.

use serde::Deserialize;

use crate::ModelError;

/// One of the three honesty levels (R2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Level {
    /// A fact reproduced from an authority. Not established here.
    SomeTrue,
    /// Constructed here and validated against its oracle.
    Build,
    /// Measured and reported, never asserted.
    Open,
}

impl Level {
    /// The token used in `model/*.toml` and in generated documentation.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SomeTrue => "some-true",
            Self::Build => "build",
            Self::Open => "open",
        }
    }
}

/// `model/ledger.toml`.
#[derive(Debug, Clone, Deserialize)]
pub struct Ledger {
    /// The schema tag.
    pub spec: String,
    /// One row per claim.
    pub claim: Vec<Claim>,
}

/// One claim, at exactly one honesty level.
#[derive(Debug, Clone, Deserialize)]
pub struct Claim {
    /// The conformance ID, or an `AUTH-`/`OPEN-` prefixed identifier.
    pub id: String,
    /// The honesty level. Untagged claims do not ship (R2).
    pub level: Level,
    /// What is claimed.
    pub statement: String,
    /// The Gherkin file carrying the scenario (R3).
    #[serde(default)]
    pub feature: Option<String>,
    /// The authority a `some-true` claim is reproduced from.
    #[serde(default)]
    pub authority: Option<String>,
    /// Recorded sample size, for a claim that is a statistic.
    #[serde(default)]
    pub sample_size: Option<u64>,
    /// Recorded seed, for a claim that is a statistic.
    #[serde(default)]
    pub seed: Option<u64>,
}

impl Ledger {
    /// The meta-gate's structural half: every claim is well formed for its
    /// level (R2).
    ///
    /// The behavioural half --- that no test asserts an `open` claim as
    /// established --- lives in `repo-conformance`, because it needs the
    /// test names, not the model.
    pub fn check(&self) -> Result<(), ModelError> {
        for c in &self.claim {
            match c.level {
                Level::SomeTrue => {
                    if c.authority.is_none() {
                        return Err(ModelError::Inconsistent(format!(
                            "{}: a some-true claim must name the authority it is \
                             reproduced from",
                            c.id
                        )));
                    }
                }
                Level::Build => {
                    if c.feature.is_none() {
                        return Err(ModelError::Inconsistent(format!(
                            "{}: a build claim must name the Gherkin scenario that \
                             validates it (R3)",
                            c.id
                        )));
                    }
                    if c.authority.is_some() {
                        return Err(ModelError::Inconsistent(format!(
                            "{}: a build claim is evidence, not a reproduction of an \
                             authority; it must not name one",
                            c.id
                        )));
                    }
                }
                Level::Open => {
                    if c.authority.is_some() {
                        return Err(ModelError::Inconsistent(format!(
                            "{}: an open claim is a measurement and cannot cite an \
                             authority for its value",
                            c.id
                        )));
                    }
                }
            }
            // No rules about a *class* of ID here. `CP-` recording a sample size,
            // `CG-` being measured rather than asserted, `CN-` not existing at
            // all --- each was a fact about a repository that had that class, and
            // a rule enforcing a taxonomy the register does not have is a
            // restriction on the first person to want one. A repository adding a
            // class adds its rule here, in the commit that adds the first ID in
            // it. The level rules above apply to every claim and stay.
        }
        Ok(())
    }

    /// Look up a claim by conformance ID.
    pub fn get(&self, id: &str) -> Option<&Claim> {
        self.claim.iter().find(|c| c.id == id)
    }
}

/// `model/ids.toml` --- the conformance ID register.
#[derive(Debug, Clone, Deserialize)]
pub struct Ids {
    /// The schema tag.
    pub spec: String,
    /// One row per conformance ID.
    pub id: Vec<IdRow>,
}

/// One registered conformance ID.
#[derive(Debug, Clone, Deserialize)]
pub struct IdRow {
    /// The ID, e.g. `CS-04`.
    pub id: String,
    /// The honesty level of the claim (R2).
    pub level: Level,
    /// The Gherkin suite the scenario belongs to.
    pub suite: String,
    /// What the ID claims.
    pub statement: String,
}

impl Ids {
    /// Look up a row.
    pub fn get(&self, id: &str) -> Option<&IdRow> {
        self.id.iter().find(|r| r.id == id)
    }
}

/// `model/authorities.toml` --- what this repository cites (`CM-03`).
#[derive(Debug, Clone, Deserialize)]
pub struct Authorities {
    /// The schema tag.
    pub spec: String,
    /// One row per cited authority.
    pub authority: Vec<AuthorityRow>,
}

/// A cited authority. Never re-derived, vendored, or gated on.
#[derive(Debug, Clone, Deserialize)]
pub struct AuthorityRow {
    /// Stable identifier, e.g. `CL-MM01`.
    pub id: String,
    /// Human-readable name.
    pub name: String,
    /// What a third party needs to find the source.
    pub citation: String,
    /// A checksum over the committed artifact, or `none`.
    pub checksum: String,
    /// Why there is no checksum, when there is none.
    #[serde(default)]
    pub checksum_reason: String,
    /// What the authority says.
    pub statement: String,
    /// The conformance IDs that are evidence this library realizes it.
    #[serde(default)]
    pub realized_by: Vec<String>,
}

/// `model/errors.toml` --- the closed public diagnostic registry (§26.1).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Errors {
    /// The schema tag, `lexlean/errors/1`.
    pub spec: String,
    /// One row per registered code, sorted by code.
    #[serde(rename = "error")]
    pub error: Vec<ErrorRow>,
}

/// One registered diagnostic code.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ErrorRow {
    /// The code, e.g. `LLL1004`.
    pub code: String,
    /// The failure class token.
    pub class: String,
    /// The sanctioned exit code.
    pub exit: u8,
    /// The short title.
    pub title: String,
    /// The registered meaning.
    pub statement: String,
}

impl Errors {
    /// Look up a row.
    pub fn get(&self, code: &str) -> Option<&ErrorRow> {
        self.error.iter().find(|row| row.code == code)
    }

    /// The structural checks of §26.1: sorted unique codes, the exact
    /// class/exit pairing, range letters agreeing with classes, nonempty
    /// statements.
    pub fn check(&self) -> Result<(), ModelError> {
        let bad = |m: String| ModelError::Inconsistent(m);
        if self.spec != "lexlean/errors/1" {
            return Err(bad(format!("errors.toml has spec `{}`", self.spec)));
        }
        let mut previous: Option<&str> = None;
        for row in &self.error {
            if let Some(before) = previous {
                if before >= row.code.as_str() {
                    return Err(bad(format!(
                        "error rows must sort by code; `{}` follows `{before}`",
                        row.code
                    )));
                }
            }
            previous = Some(&row.code);
            let bytes = row.code.as_bytes();
            let shape_ok = bytes.len() == 7
                && bytes[0] == b'L'
                && bytes[1] == b'L'
                && bytes[3..].iter().all(u8::is_ascii_digit);
            if !shape_ok {
                return Err(bad(format!("`{}` is not a diagnostic code", row.code)));
            }
            if row.statement.trim().is_empty() {
                return Err(bad(format!("{}: an empty statement", row.code)));
            }
            let exit_ok = matches!(
                (row.class.as_str(), row.exit),
                ("language", 1)
                    | ("cli-configuration", 2)
                    | ("environment", 3)
                    | ("security-limit", 4)
                    | ("internal", 70)
            );
            if !exit_ok {
                return Err(bad(format!(
                    "{}: class `{}` with exit {} is not a sanctioned combination",
                    row.code, row.class, row.exit
                )));
            }
        }
        Ok(())
    }
}
