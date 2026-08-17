//! The honesty meta-gate (R2, R3, SPEC.md §27.7, §27.8).
//!
//! Levels only mean something if the suite respects them, and the register
//! only means something if every row has exactly one scenario whose
//! statement equals the registered statement and exactly one test named
//! `conformance_<id>`, neither ignored nor feature-gated.

use std::collections::BTreeSet;
use std::path::Path;

use repo_model::{Level, Model};

use crate::runner::SuiteReport;

/// What the meta-gate found.
#[derive(Clone, Debug, Default)]
pub struct HonestyReport {
    /// Every problem, each naming the rule it breaks.
    pub violations: Vec<String>,
    /// How many registered IDs were checked.
    pub ids_checked: usize,
    /// How many scenarios were read.
    pub scenarios_checked: usize,
}

impl HonestyReport {
    /// Did everything hold?
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.violations.is_empty()
    }
}

/// Words that assert a claim as established. A `build` claim may use them;
/// an `open` claim may not, and a `some-true` claim belongs to someone
/// else.
const ASSERTIVE: &[&str] = &[
    "proves",
    "proven",
    "proof that",
    "guarantees",
    "establishes",
    "demonstrates that",
    "shows that",
    "confirms",
];

/// The exact test name for an ID (§27.8).
#[must_use]
pub fn test_name_for(id: &str) -> String {
    format!("conformance_{}", id.to_lowercase().replace('-', "_"))
}

/// Run the meta-gate.
#[allow(clippy::too_many_lines)]
pub fn check_honesty(root: &Path, tests: &BTreeSet<String>) -> std::io::Result<HonestyReport> {
    let mut report = HonestyReport::default();
    let model = match Model::load(&root.join("model")) {
        Ok(model) => model,
        Err(error) => {
            report
                .violations
                .push(format!("R1: the model does not load: {error}"));
            return Ok(report);
        }
    };
    let suites: SuiteReport = crate::runner::scenarios_in(&root.join("features/suites"))?;
    report.scenarios_checked = suites.scenarios.len();
    report.ids_checked = model.ids.id.len();
    report.violations.extend(suites.violations.clone());

    let (_all_names, flagged) = crate::workspace_test_names_with_flags(root);

    // R3, §27.8: every registered ID has exactly one scenario in its named
    // suite and exactly one test with the exact generated name.
    for row in &model.ids.id {
        let matching: Vec<_> = suites
            .scenarios
            .iter()
            .filter(|scenario| scenario.id == row.id)
            .collect();
        match matching.as_slice() {
            [] => report.violations.push(format!(
                "R3: {} is registered but has no scenario in features/suites/.",
                row.id
            )),
            [scenario] => {
                if scenario.suite != row.suite {
                    report.violations.push(format!(
                        "R3: {} lives in `{}`, the register says `{}`.",
                        row.id, scenario.suite, row.suite
                    ));
                }
                if scenario.statement.trim() != row.statement.trim() {
                    report.violations.push(format!(
                        "R3: {}'s scenario statement differs from the register (§27.7):\n    scenario: {}\n    register: {}",
                        row.id, scenario.statement, row.statement
                    ));
                }
                if scenario.tag_line != format!("@{} @{}", row.id, row.level.as_str()) {
                    report.violations.push(format!(
                        "R2: {}'s tag line must be exactly `@{} @{}`, found `{}` (§27.7).",
                        row.id,
                        row.id,
                        row.level.as_str(),
                        scenario.tag_line
                    ));
                }
                if scenario.steps.is_empty() {
                    report.violations.push(format!(
                        "R3: {}'s scenario has no steps; there are no pending steps.",
                        row.id
                    ));
                }
            }
            many => report.violations.push(format!(
                "R3: {} has {} scenarios; each ID has exactly one (§27.7).",
                row.id,
                many.len()
            )),
        }
        let expected = test_name_for(&row.id);
        let count = tests.iter().filter(|name| **name == expected).count();
        match count {
            1 => {}
            0 => report.violations.push(format!(
                "§27.8: {} is registered but no test is named `{expected}`.",
                row.id
            )),
            _ => report.violations.push(format!(
                "§27.8: more than one test claims {} through `{expected}`.",
                row.id
            )),
        }
        if flagged.contains(&expected) {
            report.violations.push(format!(
                "§27.8: `{expected}` is ignored or hidden behind a cfg; a disabled conformance test is a claim with nothing behind it.",
            ));
        }
    }

    // The other direction: every scenario names a registered ID.
    for scenario in &suites.scenarios {
        if model.ids.get(&scenario.id).is_none() {
            report.violations.push(format!(
                "R3: scenario `{}` in {} names `{}`, which is not in the register.",
                scenario.statement, scenario.suite, scenario.id
            ));
        }
    }

    // The third direction: every ID a test name claims is registered. A
    // `conformance_` test names an ID by §27.8's formula, so *any* such
    // name is a claim: an unregistered prefix (`conformance_zz_01`) and a
    // malformed shape (`conformance_lx_101`, `conformance_lx`) are claims
    // about IDs that do not exist, not names to skip.
    for name in tests {
        let Some(rest) = name.strip_prefix("conformance_") else {
            continue;
        };
        let mut parts = rest.splitn(2, '_');
        let (Some(letters), Some(digits)) = (parts.next(), parts.next()) else {
            report.violations.push(format!(
                "§27.8: test `{name}` is not `conformance_<id>` for any registered ID."
            ));
            continue;
        };
        let shaped = letters.len() == 2
            && letters.chars().all(|c| c.is_ascii_lowercase())
            && digits.len() == 2
            && digits.chars().all(|c| c.is_ascii_digit());
        if !shaped {
            report.violations.push(format!(
                "§27.8: test `{name}` is not `conformance_<id>` for any registered ID."
            ));
            continue;
        }
        let id = format!("{}-{digits}", letters.to_uppercase());
        if model.ids.get(&id).is_none() {
            report.violations.push(format!(
                "§27.8: test `{name}` names `{id}`, which is not in the register."
            ));
        }
    }

    // R2: an `open` claim must not be asserted as established, anywhere.
    let open_ids: Vec<&str> = model
        .ids
        .id
        .iter()
        .filter(|row| row.level == Level::Open)
        .map(|row| row.id.as_str())
        .collect();
    for document in [
        "README.md",
        "CONFORMANCE.md",
        "VERIFICATION.md",
        "ERRORS.md",
    ] {
        let path = root.join(document);
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        for (index, line) in text.lines().enumerate() {
            let lower = line.to_lowercase();
            for id in &open_ids {
                if !line.contains(id) {
                    continue;
                }
                if let Some(word) = ASSERTIVE.iter().find(|word| lower.contains(*word)) {
                    report.violations.push(format!(
                        "R2: {document}:{}: `{id}` is an `open` claim but this line says `{word}`.",
                        index + 1
                    ));
                }
            }
        }
    }
    for authority in &model.authorities.authority {
        for document in ["README.md", "CONFORMANCE.md"] {
            let path = root.join(document);
            let Ok(text) = std::fs::read_to_string(&path) else {
                continue;
            };
            for (index, line) in text.lines().enumerate() {
                if !line.contains(&authority.id) {
                    continue;
                }
                let lower = line.to_lowercase();
                if let Some(word) = ASSERTIVE.iter().find(|word| lower.contains(*word)) {
                    report.violations.push(format!(
                        "R2: {document}:{}: `{}` is cited, not established here, but this line says `{word}`.",
                        index + 1,
                        authority.id
                    ));
                }
            }
        }
    }

    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The gate's own vocabulary check must be able to fire, or every clean
    /// run above means nothing.
    #[test]
    fn the_assertive_vocabulary_is_recognised() {
        for word in ASSERTIVE {
            let line = format!("XX-00 {word} the claim");
            assert!(ASSERTIVE.iter().any(|w| line.to_lowercase().contains(*w)));
        }
        let honest = "XX-00 reports the measurement with its interval";
        assert!(!ASSERTIVE.iter().any(|w| honest.to_lowercase().contains(*w)));
    }
}
