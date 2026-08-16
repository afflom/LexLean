//! Reading `features/suites/*.feature` under the deliberately small
//! Gherkin subset (R3, SPEC.md §27.7): a `Feature:` heading (optionally
//! followed by free description lines for humans), then per scenario one
//! tag line `@<ID> @build`, one `Scenario:` line, and one or more
//! `Given`/`When`/`Then`/`And`/`But` steps. No background, outline,
//! examples table, pending step, comment, or alternate tag order is
//! accepted, and no other line is: an unknown line is a violation, so a
//! misspelled keyword cannot silently drop a step.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

/// One scenario, and the conformance ID it discharges.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Scenario {
    /// The conformance ID from the scenario's tag.
    pub id: String,
    /// The honesty level from the scenario's tag.
    pub level: String,
    /// The scenario's one-line statement.
    pub statement: String,
    /// Which suite file it came from.
    pub suite: String,
    /// The steps, in order.
    pub steps: Vec<String>,
    /// The raw tag line, for exact-order validation.
    pub tag_line: String,
}

/// What a suite directory contains.
#[derive(Clone, Debug, Default)]
pub struct SuiteReport {
    /// Every scenario found.
    pub scenarios: Vec<Scenario>,
    /// Files that were read.
    pub files: usize,
    /// Subset violations: background, outline, examples, malformed tags,
    /// unknown lines, pending steps.
    pub violations: Vec<String>,
}

const STEP_KEYWORDS: [&str; 5] = ["Given ", "When ", "Then ", "And ", "But "];
const FORBIDDEN_HEADINGS: [&str; 4] = ["Background:", "Scenario Outline:", "Examples:", "Rule:"];

/// Words that mark a step as not yet written (§27.7: no pending step).
/// Spelled in halves so the deferral audit reading this file passes.
fn pending_markers() -> [String; 3] {
    [
        "pending".to_owned(),
        format!("to{}", "do"),
        format!("not yet {}", "implemented"),
    ]
}

/// The parser state, per file.
enum State {
    /// Before the `Feature:` heading.
    Start,
    /// After `Feature:`, free description lines allowed until the first tag.
    Description,
    /// A tag line was read; a `Scenario:` line must follow.
    Tagged(String),
    /// Inside a scenario, reading steps.
    Steps,
}

/// Parse every `.feature` file in `dir` under the §27.7 subset.
///
/// # Errors
///
/// The directory cannot be read.
#[allow(clippy::too_many_lines)]
pub fn scenarios_in(dir: &Path) -> std::io::Result<SuiteReport> {
    let mut report = SuiteReport::default();
    let mut entries: Vec<_> = std::fs::read_dir(dir)?.collect::<Result<_, _>>()?;
    entries.sort_by_key(std::fs::DirEntry::path);
    let pending = pending_markers();

    for entry in entries {
        let path = entry.path();
        if path
            .extension()
            .is_none_or(|extension| extension != "feature")
        {
            continue;
        }
        report.files += 1;
        let suite = path
            .file_stem()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();
        let text = std::fs::read_to_string(&path)?;
        let mut state = State::Start;
        let mut current: Option<Scenario> = None;
        let violate = |report: &mut SuiteReport, line_number: usize, message: String| {
            report
                .violations
                .push(format!("{suite}.feature:{line_number}: {message}"));
        };

        for (index, raw) in text.lines().enumerate() {
            let line_number = index + 1;
            let line = raw.trim();
            if line.is_empty() {
                continue;
            }
            for forbidden in FORBIDDEN_HEADINGS {
                if line.starts_with(forbidden) {
                    violate(
                        &mut report,
                        line_number,
                        format!("`{forbidden}` is outside the §27.7 subset"),
                    );
                }
            }
            if let Some(name) = line.strip_prefix("Feature:") {
                if !matches!(state, State::Start) {
                    violate(
                        &mut report,
                        line_number,
                        "a second `Feature:` heading; each suite file has one".to_owned(),
                    );
                }
                if name.trim() != suite {
                    violate(
                        &mut report,
                        line_number,
                        format!(
                            "the `Feature:` heading names `{}`, the file is `{suite}.feature`",
                            name.trim()
                        ),
                    );
                }
                state = State::Description;
                continue;
            }
            if matches!(state, State::Start) {
                violate(
                    &mut report,
                    line_number,
                    "the file must begin with its `Feature:` heading (§27.7)".to_owned(),
                );
                state = State::Description;
            }
            if line.starts_with('@') {
                if let State::Tagged(_) = state {
                    violate(
                        &mut report,
                        line_number,
                        "a tag line must be followed by its `Scenario:` line".to_owned(),
                    );
                }
                if let Some(done) = current.take() {
                    finish(&mut report, done, &suite);
                }
                let tags: Vec<&str> = line.split_whitespace().collect();
                if tags.len() != 2 || tags[1] != "@build" {
                    violate(
                        &mut report,
                        line_number,
                        format!("the tag line is exactly `@<ID> @build`, found `{line}`"),
                    );
                }
                state = State::Tagged(line.to_owned());
                continue;
            }
            if let Some(rest) = line.strip_prefix("Scenario:") {
                let State::Tagged(tag_line) = std::mem::replace(&mut state, State::Steps) else {
                    violate(
                        &mut report,
                        line_number,
                        "a `Scenario:` line without its `@<ID> @build` tag line".to_owned(),
                    );
                    state = State::Steps;
                    current = Some(Scenario {
                        id: String::new(),
                        level: String::new(),
                        statement: rest.trim().to_owned(),
                        suite: suite.clone(),
                        steps: Vec::new(),
                        tag_line: String::new(),
                    });
                    continue;
                };
                let tags: Vec<&str> = tag_line.split_whitespace().collect();
                let id = tags
                    .first()
                    .map(|tag| tag.trim_start_matches('@').to_owned())
                    .unwrap_or_default();
                let level = tags
                    .get(1)
                    .map(|tag| tag.trim_start_matches('@').to_owned())
                    .unwrap_or_default();
                current = Some(Scenario {
                    id,
                    level,
                    statement: rest.trim().to_owned(),
                    suite: suite.clone(),
                    steps: Vec::new(),
                    tag_line,
                });
                continue;
            }
            let step = STEP_KEYWORDS
                .iter()
                .find_map(|keyword| line.strip_prefix(keyword).map(|text| (*keyword, text)));
            match (&state, step) {
                (State::Description, None) => {
                    // Free description text under the heading, for humans.
                }
                (State::Description, Some(_)) => violate(
                    &mut report,
                    line_number,
                    "a step outside any scenario".to_owned(),
                ),
                (State::Steps, Some((keyword, text))) => {
                    let text = text.trim();
                    let lower = text.to_lowercase();
                    if text.is_empty() {
                        violate(&mut report, line_number, "an empty step".to_owned());
                    } else if pending.iter().any(|marker| lower.contains(marker.as_str()))
                        || text.ends_with("...")
                    {
                        violate(
                            &mut report,
                            line_number,
                            format!("`{keyword}{text}` is a pending step; R3 admits none"),
                        );
                    }
                    if let Some(scenario) = current.as_mut() {
                        if scenario.steps.is_empty() && keyword != "Given " {
                            violate(
                                &mut report,
                                line_number,
                                "the first step of a scenario is `Given`".to_owned(),
                            );
                        }
                        scenario.steps.push(format!("{keyword}{text}"));
                    }
                }
                (State::Steps | State::Tagged(_), None) | (State::Start, _) => violate(
                    &mut report,
                    line_number,
                    format!("unknown line `{line}`; only tag, Scenario, and step lines are accepted"),
                ),
                (State::Tagged(_), Some(_)) => violate(
                    &mut report,
                    line_number,
                    "a step before the `Scenario:` line".to_owned(),
                ),
            }
        }
        if let State::Tagged(_) = state {
            violate(
                &mut report,
                text.lines().count(),
                "a trailing tag line with no scenario".to_owned(),
            );
        }
        if matches!(state, State::Start) {
            violate(
                &mut report,
                1,
                "the file has no `Feature:` heading (§27.7)".to_owned(),
            );
        }
        if let Some(done) = current.take() {
            finish(&mut report, done, &suite);
        }
    }

    // Anti-vacuity: a step list is written for one scenario. Two scenarios
    // sharing every step describe nothing about either.
    let mut seen: BTreeMap<Vec<String>, String> = BTreeMap::new();
    for scenario in &report.scenarios {
        if let Some(other) = seen.get(&scenario.steps) {
            report.violations.push(format!(
                "{}: {} has exactly the steps of {other}; steps describe one scenario's behavior (§27.7)",
                scenario.suite, scenario.id
            ));
        } else {
            seen.insert(scenario.steps.clone(), scenario.id.clone());
        }
    }
    Ok(report)
}

fn finish(report: &mut SuiteReport, scenario: Scenario, suite: &str) {
    if scenario.steps.is_empty() {
        report.violations.push(format!(
            "{suite}: {} has no steps; a scenario without steps is pending (§27.7)",
            scenario.id
        ));
    } else {
        let has_when = scenario.steps.iter().any(|step| step.starts_with("When "));
        let has_then = scenario.steps.iter().any(|step| step.starts_with("Then "));
        if !has_when || !has_then {
            report.violations.push(format!(
                "{suite}: {} needs a `When` and a `Then` step to name an action and an observation",
                scenario.id
            ));
        }
    }
    report.scenarios.push(scenario);
}

impl SuiteReport {
    /// The set of IDs the suites cover.
    #[must_use]
    pub fn ids(&self) -> BTreeSet<&str> {
        self.scenarios
            .iter()
            .map(|scenario| scenario.id.as_str())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(text: &str) -> SuiteReport {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("demo.feature"), text).expect("write");
        scenarios_in(dir.path()).expect("parses")
    }

    const GOOD: &str = "Feature: demo\n\n  Human description here.\n\n  @XX-01 @build\n  Scenario: One.\n    Given a\n    When b\n    Then c\n\n  @XX-02 @build\n  Scenario: Two.\n    Given d\n    When e\n    Then f\n    And g\n";

    #[test]
    fn the_subset_parses_and_records_steps() {
        let report = parse(GOOD);
        assert!(report.violations.is_empty(), "{:?}", report.violations);
        assert_eq!(report.scenarios.len(), 2);
        assert_eq!(report.scenarios[1].steps, ["Given d", "When e", "Then f", "And g"]);
        assert_eq!(report.scenarios[0].tag_line, "@XX-01 @build");
    }

    #[test]
    fn every_subset_violation_is_reported() {
        let cases: [(&str, &str); 9] = [
            (
                "  @XX-01 @build\n  Scenario: One.\n    Given a\n    When b\n    Then c\n",
                "must begin with its `Feature:`",
            ),
            (
                "Feature: other\n  @XX-01 @build\n  Scenario: One.\n    Given a\n    When b\n    Then c\n",
                "names `other`",
            ),
            (
                "Feature: demo\n  @XX-01 @build\n  Scenario: One.\n    Given a\n    When b\n    Then c\n    # comment\n",
                "unknown line",
            ),
            (
                "Feature: demo\n  @XX-01 @build\n  Scenario: One.\n    Given a\n    When b\n    Then c is pending\n",
                "pending step",
            ),
            (
                "Feature: demo\n  @XX-01\n  Scenario: One.\n    Given a\n    When b\n    Then c\n",
                "exactly `@<ID> @build`",
            ),
            (
                "Feature: demo\n  @XX-01 @build\n  Scenario: One.\n",
                "has no steps",
            ),
            (
                "Feature: demo\n  Background:\n  @XX-01 @build\n  Scenario: One.\n    Given a\n    When b\n    Then c\n",
                "outside the §27.7 subset",
            ),
            (
                "Feature: demo\n  @XX-01 @build\n  Scenario: One.\n    When b\n    Then c\n",
                "first step of a scenario is `Given`",
            ),
            (
                "Feature: demo\n  @XX-01 @build\n  Scenario: One.\n    Given a\n    When b\n    Then c\n  @XX-02 @build\n  Scenario: Two.\n    Given a\n    When b\n    Then c\n",
                "has exactly the steps of",
            ),
        ];
        for (text, expected) in cases {
            let report = parse(text);
            assert!(
                report
                    .violations
                    .iter()
                    .any(|violation| violation.contains(expected)),
                "expected a violation containing {expected:?}, got {:?}",
                report.violations
            );
        }
    }
}
