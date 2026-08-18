//! The honesty meta-gate against the actual workspace (R2, R3, SPEC.md
//! §27.7, §27.8): the register, the feature suites, and the test names read
//! from the source. An ID with no scenario, a scenario with no ID, an ID
//! with no test, an ignored or cfg-gated conformance test, a scenario
//! outside the Gherkin subset, or a mislabelled honesty level all fail
//! here.

use std::collections::BTreeSet;
use std::path::PathBuf;

use repo_conformance::{check_honesty, scenarios_in, workspace_test_names};
use repo_model::{Level, Model};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("crates/conformance is two below the root")
        .to_path_buf()
}

/// §27.8: every registered ID has a scenario and a test, and every scenario
/// and test names a registered ID.
#[test]
fn every_id_has_a_scenario_and_a_test() {
    let root = root();
    let tests = workspace_test_names(&root);
    assert!(!tests.is_empty(), "the test list must not be empty");

    let report = check_honesty(&root, &tests).expect("the meta-gate runs");
    assert!(
        report.is_clean(),
        "the honesty meta-gate failed:\n\n{}",
        report.violations.join("\n\n")
    );
    eprintln!(
        "meta-gate: {} registered IDs, {} scenarios, {} test names",
        report.ids_checked,
        report.scenarios_checked,
        tests.len()
    );
}

/// §27.7: the suites are inside the Gherkin subset, no step is pending,
/// and every scenario's steps are its own.
///
/// The non-emptiness guard is armed by the *register*, not asserted
/// outright: a repository with registered IDs and no feature files is the
/// defect this catches.
#[test]
fn the_suites_are_inside_the_gherkin_subset() {
    let model = Model::load(&root().join("model")).expect("model loads");
    let suites = scenarios_in(&root().join("features/suites")).expect("suites read");
    assert!(
        model.ids.id.is_empty() || suites.files >= 1,
        "{} registered IDs and no feature files",
        model.ids.id.len()
    );
    assert!(
        suites.violations.is_empty(),
        "§27.7 subset violations:\n{}",
        suites.violations.join("\n")
    );
    for scenario in &suites.scenarios {
        assert!(!scenario.steps.is_empty(), "{} has no steps", scenario.id);
        assert!(
            scenario.steps.len() <= 6,
            "{}: {} steps; a scenario states one behavior",
            scenario.id,
            scenario.steps.len()
        );
    }
}

/// §27.4: every `some-true` claim cites an authority that exists, with a
/// citation and either a checksum or a stated reason for its absence.
#[test]
fn every_some_true_claim_cites_an_authority() {
    let model = Model::load(&root().join("model")).expect("model loads");
    model.check().expect("the model is consistent");

    let mut some_true = 0usize;
    for claim in &model.ledger.claim {
        if claim.level != Level::SomeTrue {
            continue;
        }
        some_true += 1;
        let name = claim
            .authority
            .as_ref()
            .expect("a some-true claim names an authority");
        let a = model
            .authorities
            .authority
            .iter()
            .find(|a| &a.id == name)
            .unwrap_or_else(|| panic!("{name} has no row in model/authorities.toml"));
        assert!(!a.citation.trim().is_empty(), "{name} has no citation");
        assert!(
            a.checksum != "none" || !a.checksum_reason.trim().is_empty(),
            "{name} has no checksum and no reason for its absence"
        );
    }
    assert!(
        model.ledger.claim.is_empty() || some_true >= 1 || model.authorities.authority.is_empty(),
        "a ledger with claims and no cited authority"
    );
    eprintln!("§27.4: {some_true} cited authorities, each with a citation");
}

/// R2: the meta-gate can fail.
///
/// A gate nobody has ever seen fail is indistinguishable from a gate that
/// cannot. This plants the violations it exists to catch and checks that
/// each is reported: a missing test, an ignored test, a scenario whose
/// statement drifted, and a suite outside the subset.
#[test]
fn the_meta_gate_is_falsifiable() {
    let root = root();
    let model = Model::load(&root.join("model")).expect("model loads");
    assert!(
        !model.ids.id.is_empty(),
        "the register is populated, so every plant below has an ID to act on"
    );

    // An ID with no test.
    let empty = BTreeSet::new();
    let report = check_honesty(&root, &empty).expect("runs");
    assert!(!report.is_clean(), "an empty test list must fail the gate");
    assert!(
        report
            .violations
            .iter()
            .any(|v| v.contains("no test is named")),
        "the missing-test violation must be reported: {:?}",
        report.violations.first()
    );

    // A test list that covers everything passes, which is the control.
    let full = workspace_test_names(&root);
    assert!(check_honesty(&root, &full).expect("runs").is_clean());

    // A copy of the repository's model and suites with one scenario
    // statement altered, one tag line reordered, and one file given a
    // pending step: each drift is named.
    let planted = tempfile::tempdir().expect("tempdir");
    let copy = |relative: &str| {
        let from = root.join(relative);
        let to = planted.path().join(relative);
        std::fs::create_dir_all(&to).expect("mkdir");
        for entry in std::fs::read_dir(&from).expect("dir").flatten() {
            std::fs::copy(entry.path(), to.join(entry.file_name())).expect("copy");
        }
    };
    copy("model");
    copy("features/suites");
    let suite_dir = planted.path().join("features/suites");
    let repository = suite_dir.join("repository.feature");
    let text = std::fs::read_to_string(&repository).expect("suite");
    let drifted = text
        .replacen("@RP-01 @build", "@build @RP-01", 1)
        .replacen(
            "Scenario: The repository is derived from the pinned UOR template commit",
            "Scenario: The repository is derived from the chosen UOR template commit",
            1,
        )
        .replacen("    Given ", "    Given (pending) ", 1);
    assert_ne!(text, drifted, "the plants applied");
    std::fs::write(&repository, drifted).expect("write");
    let report = check_honesty(planted.path(), &full).expect("runs");
    for expected in [
        "differs from the register",
        "exactly `@<ID> @build`",
        "pending step",
    ] {
        assert!(
            report.violations.iter().any(|v| v.contains(expected)),
            "planted drift `{expected}` was not reported: {:?}",
            report.violations
        );
    }
}

/// §27.8: an ignored or cfg-gated conformance test is flagged even when
/// the attribute is not adjacent to `#[test]`.
#[test]
fn a_hidden_conformance_test_is_flagged() {
    let scanned = repo_conformance::scan_tests(&format!(
        "#[test]\n#[cfg_attr(target_os = \"windows\", {})]\nfn conformance_zz_99() {{}}\n",
        "ignore"
    ));
    assert!(scanned.names.contains("conformance_zz_99"));
    assert!(scanned.flagged.contains("conformance_zz_99"));
    let (names, flagged) = repo_conformance::workspace_test_names_with_flags(&root());
    let hidden: Vec<&String> = flagged
        .iter()
        .filter(|name| name.starts_with("conformance_"))
        .collect();
    assert!(
        hidden.is_empty(),
        "conformance tests hidden behind ignore or cfg: {hidden:?}"
    );
    assert!(
        names.len() > 210,
        "the workspace has more than the conformance tests"
    );
}
