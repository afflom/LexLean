//! The release gate (SPEC.md §30, RP-12): a release is refused unless the
//! complete §30.3 artifact set and the §30.4 completion criterion hold, each
//! checked by content rather than by existence.
//!
//! Refusal is the honest steady state until every artifact exists and every
//! criterion holds; `cargo xtask release-check` runs this (plus the crate
//! packaging round trip, which needs cargo) and fails while any criterion
//! is unmet.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// Every §30.3 release artifact and §30.4 completion criterion, by stable
/// name. The conformance suite compares this list against the specification.
pub const CRITERIA: &[(&str, &str)] = &[
    (
        "source-tag",
        "the workspace version is 1.0.0 and CHANGELOG.md has a `## 1.0.0` entry for the tagged commit",
    ),
    (
        "checksums",
        "release/checksums.txt lists `<sha256>  <path>` for every other file under release/, and every hash matches",
    ),
    (
        "host-binaries",
        "release/bin/<target>/lexlean holds a binary for each of the five supported hosts (§8.3)",
    ),
    (
        "crate-package",
        "release/lexlean.crate is the gzip-compressed packaged crate",
    ),
    (
        "semantics-id",
        "release/compiler-semantics-id.txt is one 64-hex-digit line",
    ),
    (
        "version-output",
        "release/version-output.txt is the exact four-line `lexlean --version` output of §30.3 with the release version and the semantics ID",
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
        "release/sbom.json is a CycloneDX or SPDX software bill of materials that lists the lexlean package",
    ),
    (
        "ci-evidence",
        "release/vv-evidence.txt records `just vv` passing and names the tagged commit",
    ),
    (
        "no-ignored-test",
        "no test in the workspace is ignored or hidden behind a cfg (§30.4)",
    ),
    (
        "gate-evidence",
        "VERIFICATION.md carries a falsifiability record for every gate and audit (§27.9, §30.4)",
    ),
    (
        "schemas-exercised",
        "every committed schema is validated against an artifact by the conformance suite (§30.4)",
    ),
];

/// The version §2.3 fixes as the first release satisfying the complete
/// specification.
pub const RELEASE_VERSION: &str = "1.0.0";

/// The five supported hosts of §8.3 as Rust target triples.
pub const HOST_TARGETS: [&str; 5] = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "x86_64-apple-darwin",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
];

/// The gates and audits that need a falsifiability record (§27.9): every
/// `vv` recipe, every `validate-model` sub-audit, and the two gates outside
/// `vv`.
pub const GATES: [&str; 22] = [
    "fmt-check",
    "validate-model",
    "audit-deferral",
    "audit-errors",
    "audit-shipped",
    "audit-generated",
    "audit-language-closure",
    "audit-no-unsafe",
    "honesty-vocabulary",
    "meta-gate",
    "model-unknown-field",
    "spec-links",
    "lint",
    "test",
    "features",
    "bdd",
    "verify-examples",
    "check-golden",
    "check-reproducibility",
    "deny",
    "release-check",
    "check-fixtures",
];

fn is_hex(text: &str, length: usize) -> bool {
    text.len() == length && text.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn files_under(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(current) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&current) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.is_file() {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

fn sha256_hex(bytes: &[u8]) -> String {
    // A dependency-free SHA-256 (FIPS 180-4) so this crate stays
    // build-time only; the shipped crate's implementation is independent.
    const K: [u32; 64] = [
        0x428a_2f98,
        0x7137_4491,
        0xb5c0_fbcf,
        0xe9b5_dba5,
        0x3956_c25b,
        0x59f1_11f1,
        0x923f_82a4,
        0xab1c_5ed5,
        0xd807_aa98,
        0x1283_5b01,
        0x2431_85be,
        0x550c_7dc3,
        0x72be_5d74,
        0x80de_b1fe,
        0x9bdc_06a7,
        0xc19b_f174,
        0xe49b_69c1,
        0xefbe_4786,
        0x0fc1_9dc6,
        0x240c_a1cc,
        0x2de9_2c6f,
        0x4a74_84aa,
        0x5cb0_a9dc,
        0x76f9_88da,
        0x983e_5152,
        0xa831_c66d,
        0xb003_27c8,
        0xbf59_7fc7,
        0xc6e0_0bf3,
        0xd5a7_9147,
        0x06ca_6351,
        0x1429_2967,
        0x27b7_0a85,
        0x2e1b_2138,
        0x4d2c_6dfc,
        0x5338_0d13,
        0x650a_7354,
        0x766a_0abb,
        0x81c2_c92e,
        0x9272_2c85,
        0xa2bf_e8a1,
        0xa81a_664b,
        0xc24b_8b70,
        0xc76c_51a3,
        0xd192_e819,
        0xd699_0624,
        0xf40e_3585,
        0x106a_a070,
        0x19a4_c116,
        0x1e37_6c08,
        0x2748_774c,
        0x34b0_bcb5,
        0x391c_0cb3,
        0x4ed8_aa4a,
        0x5b9c_ca4f,
        0x682e_6ff3,
        0x748f_82ee,
        0x78a5_636f,
        0x84c8_7814,
        0x8cc7_0208,
        0x90be_fffa,
        0xa450_6ceb,
        0xbef9_a3f7,
        0xc671_78f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09_e667,
        0xbb67_ae85,
        0x3c6e_f372,
        0xa54f_f53a,
        0x510e_527f,
        0x9b05_688c,
        0x1f83_d9ab,
        0x5be0_cd19,
    ];
    let mut message = bytes.to_vec();
    let bit_length = (bytes.len() as u64).wrapping_mul(8);
    message.push(0x80);
    while message.len() % 64 != 56 {
        message.push(0);
    }
    message.extend_from_slice(&bit_length.to_be_bytes());
    for chunk in message.chunks(64) {
        let mut w = [0u32; 64];
        for (index, word) in w.iter_mut().enumerate().take(16) {
            *word = u32::from_be_bytes([
                chunk[index * 4],
                chunk[index * 4 + 1],
                chunk[index * 4 + 2],
                chunk[index * 4 + 3],
            ]);
        }
        for index in 16..64 {
            let s0 = w[index - 15].rotate_right(7)
                ^ w[index - 15].rotate_right(18)
                ^ (w[index - 15] >> 3);
            let s1 = w[index - 2].rotate_right(17)
                ^ w[index - 2].rotate_right(19)
                ^ (w[index - 2] >> 10);
            w[index] = w[index - 16]
                .wrapping_add(s0)
                .wrapping_add(w[index - 7])
                .wrapping_add(s1);
        }
        let mut a = h;
        for index in 0..64 {
            let s1 = a[4].rotate_right(6) ^ a[4].rotate_right(11) ^ a[4].rotate_right(25);
            let ch = (a[4] & a[5]) ^ (!a[4] & a[6]);
            let temp1 = a[7]
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[index])
                .wrapping_add(w[index]);
            let s0 = a[0].rotate_right(2) ^ a[0].rotate_right(13) ^ a[0].rotate_right(22);
            let maj = (a[0] & a[1]) ^ (a[0] & a[2]) ^ (a[1] & a[2]);
            let temp2 = s0.wrapping_add(maj);
            a = [
                temp1.wrapping_add(temp2),
                a[0],
                a[1],
                a[2],
                a[3].wrapping_add(temp1),
                a[4],
                a[5],
                a[6],
            ];
        }
        for (state, value) in h.iter_mut().zip(a) {
            *state = state.wrapping_add(value);
        }
    }
    h.iter().map(|word| format!("{word:08x}")).collect()
}

/// Check the complete release criterion. Returns every unmet criterion;
/// an empty error list never escapes (that would be `Ok`).
///
/// # Errors
///
/// The list of unmet criteria, each `name: requirement`.
#[allow(clippy::too_many_lines)]
pub fn check(root: &Path, hidden_tests: &BTreeSet<String>) -> Result<(), Vec<String>> {
    let mut unmet = Vec::new();
    let mut fail = |name: &str, detail: String| unmet.push(format!("{name}: {detail}"));
    let read = |relative: &str| std::fs::read_to_string(root.join(relative));

    // §2.3/§30: the workspace version must be the release version, and the
    // changelog must carry the release entry.
    let workspace = read("Cargo.toml").unwrap_or_default();
    if !workspace.contains(&format!("version = \"{RELEASE_VERSION}\"")) {
        fail(
            "source-tag",
            format!(
                "the workspace version is not {RELEASE_VERSION}; §2.3 fixes the first complete release at {RELEASE_VERSION}"
            ),
        );
    }
    match read("CHANGELOG.md") {
        Ok(changelog)
            if changelog
                .lines()
                .any(|line| line.trim() == format!("## {RELEASE_VERSION}")) => {}
        Ok(_) => fail(
            "source-tag",
            format!("CHANGELOG.md has no `## {RELEASE_VERSION}` entry"),
        ),
        Err(error) => fail("source-tag", format!("CHANGELOG.md: {error}")),
    }

    // Checksums: every other release file listed with a matching hash.
    let release_dir = root.join("release");
    match read("release/checksums.txt") {
        Ok(text) => {
            let mut listed: BTreeSet<String> = BTreeSet::new();
            for (index, line) in text.lines().enumerate() {
                let Some((hash, path)) = line.split_once("  ") else {
                    fail(
                        "checksums",
                        format!("line {}: not `<sha256>  <path>`", index + 1),
                    );
                    continue;
                };
                if !is_hex(hash, 64) {
                    fail(
                        "checksums",
                        format!("line {}: `{hash}` is not a SHA-256", index + 1),
                    );
                    continue;
                }
                match std::fs::read(release_dir.join(path)) {
                    Ok(bytes) if sha256_hex(&bytes) == hash => {}
                    Ok(_) => fail("checksums", format!("{path}: hash mismatch")),
                    Err(error) => fail("checksums", format!("{path}: {error}")),
                }
                listed.insert(path.to_owned());
            }
            for file in files_under(&release_dir) {
                let relative = file
                    .strip_prefix(&release_dir)
                    .unwrap_or(&file)
                    .to_string_lossy()
                    .replace('\\', "/");
                if relative != "checksums.txt" && !listed.contains(&relative) {
                    fail("checksums", format!("{relative} is not listed"));
                }
            }
        }
        Err(error) => fail("checksums", format!("release/checksums.txt: {error}")),
    }

    // Host binaries for the five supported hosts.
    for target in HOST_TARGETS {
        let name = if target.contains("windows") {
            "lexlean.exe"
        } else {
            "lexlean"
        };
        let path = release_dir.join("bin").join(target).join(name);
        match std::fs::metadata(&path) {
            Ok(metadata) if metadata.is_file() && metadata.len() > 0 => {}
            _ => fail(
                "host-binaries",
                format!("release/bin/{target}/{name} is missing or empty"),
            ),
        }
    }

    // The crate package is a gzip archive.
    match std::fs::read(release_dir.join("lexlean.crate")) {
        Ok(bytes) if bytes.len() > 2 && bytes[0] == 0x1f && bytes[1] == 0x8b => {}
        Ok(_) => fail(
            "crate-package",
            "release/lexlean.crate is not a gzip archive".to_owned(),
        ),
        Err(error) => fail("crate-package", format!("release/lexlean.crate: {error}")),
    }

    // The semantics ID and the four-line version output.
    let semantics = read("release/compiler-semantics-id.txt")
        .map(|text| text.trim().to_owned())
        .unwrap_or_default();
    if !is_hex(&semantics, 64) {
        fail(
            "semantics-id",
            "release/compiler-semantics-id.txt is not one 64-hex-digit line".to_owned(),
        );
    }
    match read("release/version-output.txt") {
        Ok(text) => {
            let expected = format!(
                "lexlean {RELEASE_VERSION}\nlanguage 1.0\ncompiler-semantics {semantics}\nlean-toolchain leanprover/lean4:v4.32.1\n"
            );
            if text != expected {
                fail(
                    "version-output",
                    format!(
                        "release/version-output.txt must be exactly:\n{expected}found:\n{text}"
                    ),
                );
            }
        }
        Err(error) => fail(
            "version-output",
            format!("release/version-output.txt: {error}"),
        ),
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

    // The SBOM: CycloneDX (`bomFormat`) or SPDX (`spdxVersion`) naming lexlean.
    match read("release/sbom.json") {
        Ok(text) => {
            let cyclonedx = text.contains("\"bomFormat\"") && text.contains("\"components\"");
            let spdx = text.contains("\"spdxVersion\"") && text.contains("\"packages\"");
            if !(cyclonedx || spdx) {
                fail(
                    "sbom",
                    "release/sbom.json is neither CycloneDX nor SPDX".to_owned(),
                );
            }
            if !text.contains("\"lexlean\"") {
                fail(
                    "sbom",
                    "release/sbom.json does not list the lexlean package".to_owned(),
                );
            }
        }
        Err(error) => fail("sbom", format!("release/sbom.json: {error}")),
    }

    // CI evidence: the gate passed on a named commit.
    match read("release/vv-evidence.txt") {
        Ok(text) => {
            if !text.contains("vv: the acceptance gate passed") {
                fail(
                    "ci-evidence",
                    "release/vv-evidence.txt does not record the gate passing".to_owned(),
                );
            }
            if !text.split_whitespace().any(|token| is_hex(token, 40)) {
                fail(
                    "ci-evidence",
                    "release/vv-evidence.txt names no commit".to_owned(),
                );
            }
        }
        Err(error) => fail("ci-evidence", format!("release/vv-evidence.txt: {error}")),
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
                match read(path) {
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

    // §30.4: no ignored or cfg-hidden test. The caller supplies the set
    // the attribute-block scanner flagged (the same scan the honesty
    // meta-gate runs), so a test hidden by any attribute form — `#[ignore]`,
    // `#[ignore = "..."]`, `#[cfg_attr(..., ignore)]`, a `#[cfg]` on the
    // test, its inline module, or the `mod` declaration that includes its
    // file — fails the criterion, not just the two spellings a line scan
    // can see.
    for name in hidden_tests {
        fail(
            "no-ignored-test",
            format!("`{name}` is ignored or hidden behind a cfg"),
        );
    }

    // §27.9: a falsifiability record per gate.
    match read("VERIFICATION.md") {
        Ok(text) => {
            for gate in GATES {
                let heading = format!("### {gate} can fail");
                if !text.lines().any(|line| line.starts_with(&heading)) {
                    fail(
                        "gate-evidence",
                        format!("VERIFICATION.md has no `{heading}` record"),
                    );
                }
            }
        }
        Err(error) => fail("gate-evidence", format!("VERIFICATION.md: {error}")),
    }

    // §30.4: every schema is exercised by a conformance case.
    let conformance_source: String = files_under(&root.join("crates/conformance/src"))
        .into_iter()
        .filter_map(|path| std::fs::read_to_string(path).ok())
        .collect();
    for entry in std::fs::read_dir(root.join("schemas"))
        .into_iter()
        .flatten()
        .flatten()
    {
        let file_name = entry.file_name().to_string_lossy().into_owned();
        let Some(name) = file_name.strip_suffix(".schema.json") else {
            continue;
        };
        if !conformance_source.contains(&format!("\"{name}\"")) {
            fail(
                "schemas-exercised",
                format!("schemas/{file_name} is validated by no conformance case"),
            );
        }
    }

    if unmet.is_empty() {
        Ok(())
    } else {
        Err(unmet)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_local_sha256_agrees_with_the_test_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        let long = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        assert_eq!(
            sha256_hex(long.as_bytes()),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }
}
