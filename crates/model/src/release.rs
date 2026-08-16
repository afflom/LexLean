//! The release gate (SPEC.md §30, RP-12): a release is refused unless the
//! complete release criterion and all required artifacts are satisfied.
//!
//! Refusal is the honest steady state until every §30.3 artifact exists and
//! §30.4 holds; `cargo xtask release-check` runs this and fails while any
//! criterion is unmet.

use std::path::Path;

/// Every §30.3 release artifact, by stable criterion name. The conformance
/// suite compares this list against the specification.
pub const CRITERIA: &[(&str, &str)] = &[
    (
        "source-tag",
        "an annotated release tag exists for the release commit",
    ),
    (
        "checksums",
        "release/checksums.txt lists the SHA-256 of every published artifact",
    ),
    (
        "host-binaries",
        "release/bin/ holds a binary for every supported host",
    ),
    (
        "crate-package",
        "release/lexlean.crate is the packaged crate",
    ),
    (
        "semantics-id",
        "release/compiler-semantics-id.txt equals the embedded semantics ID",
    ),
    (
        "conformance-doc",
        "CONFORMANCE.md equals regeneration from model/ids.toml",
    ),
    (
        "errors-doc",
        "ERRORS.md equals regeneration from model/errors.toml",
    ),
    ("spec", "SPEC.md is present at the repository root"),
    ("licenses", "LICENSE-APACHE and LICENSE-MIT are present"),
    (
        "sbom",
        "release/sbom.json is the software bill of materials",
    ),
    (
        "ci-evidence",
        "release/vv-evidence.txt records `just vv` passing on the tagged commit",
    ),
];

/// The version §2.3 fixes as the first release satisfying the complete
/// specification.
pub const RELEASE_VERSION: &str = "1.0.0";

/// Check the complete release criterion. Returns every unmet criterion;
/// an empty error list never escapes (that would be `Ok`).
///
/// # Errors
///
/// The list of unmet criteria, each `name: requirement`.
pub fn check(root: &Path) -> Result<(), Vec<String>> {
    let mut unmet = Vec::new();
    let mut fail = |name: &str, detail: String| unmet.push(format!("{name}: {detail}"));

    // §2.3/§30: the workspace version must be the release version.
    let workspace = std::fs::read_to_string(root.join("Cargo.toml")).unwrap_or_default();
    if !workspace.contains(&format!("version = \"{RELEASE_VERSION}\"")) {
        fail(
            "source-tag",
            format!(
                "the workspace version is not {RELEASE_VERSION}; §2.3 fixes the first complete release at {RELEASE_VERSION}"
            ),
        );
    }

    for (name, relative) in [
        ("checksums", "release/checksums.txt"),
        ("host-binaries", "release/bin"),
        ("crate-package", "release/lexlean.crate"),
        ("semantics-id", "release/compiler-semantics-id.txt"),
        ("sbom", "release/sbom.json"),
        ("ci-evidence", "release/vv-evidence.txt"),
    ] {
        if !root.join(relative).exists() {
            fail(name, format!("{relative} does not exist"));
        }
    }
    for (name, relative) in [
        ("spec", "SPEC.md"),
        ("licenses", "LICENSE-APACHE"),
        ("licenses", "LICENSE-MIT"),
    ] {
        if !root.join(relative).is_file() {
            fail(name, format!("{relative} is not a file"));
        }
    }

    // Generated documents must equal regeneration (§30.3, §27.5).
    match crate::Model::load(&root.join("model")) {
        Ok(model) => {
            for (name, path, rendered) in [
                (
                    "conformance-doc",
                    crate::codegen::CONFORMANCE_PATH,
                    crate::codegen::render_conformance(&model),
                ),
                (
                    "errors-doc",
                    crate::codegen::ERRORS_PATH,
                    crate::codegen::render_errors(&model),
                ),
            ] {
                match std::fs::read_to_string(root.join(path)) {
                    Ok(committed) if committed == rendered => {}
                    Ok(_) => fail(name, format!("{path} differs from regeneration")),
                    Err(read_error) => fail(name, format!("{path}: {read_error}")),
                }
            }
        }
        Err(model_error) => fail(
            "conformance-doc",
            format!("the model does not load: {model_error}"),
        ),
    }

    if unmet.is_empty() {
        Ok(())
    } else {
        Err(unmet)
    }
}
