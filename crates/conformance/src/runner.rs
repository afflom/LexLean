//! Reading `features/suites/*.feature` under the deliberately small
//! Gherkin subset (R3, SPEC.md §27.7): a `Feature:` heading, one tag line
//! `@<ID> @build` per scenario, one `Scenario:` line, and one or more
//! steps. No background, outline, examples table, pending step, or
//! alternate tag order is accepted.

use std::collections::BTreeSet;
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
    /// Subset violations: background, outline, examples, or malformed tags.
    pub violations: Vec<String>,
}

/// Parse every `.feature` file in `dir` under the §27.7 subset.
pub fn scenarios_in(dir: &Path) -> std::io::Result<SuiteReport> {
    let mut report = SuiteReport::default();
    let mut entries: Vec<_> = std::fs::read_dir(dir)?.collect::<Result<_, _>>()?;
    entries.sort_by_key(std::fs::DirEntry::path);

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

        let mut pending_tag: Option<String> = None;
        let mut current: Option<Scenario> = None;
        for raw in text.lines() {
            let line = raw.trim();
            for forbidden in ["Background:", "Scenario Outline:", "Examples:"] {
                if line.starts_with(forbidden) {
                    report.violations.push(format!(
                        "{suite}: `{forbidden}` is outside the §27.7 subset"
                    ));
                }
            }
            if line.starts_with('@') {
                pending_tag = Some(line.to_owned());
            } else if let Some(rest) = line.strip_prefix("Scenario:") {
                if let Some(done) = current.take() {
                    report.scenarios.push(done);
                }
                let tag_line = pending_tag.take().unwrap_or_default();
                let tags: Vec<&str> = tag_line.split_whitespace().collect();
                let id = tags
                    .first()
                    .map(|tag| tag.trim_start_matches('@').to_owned())
                    .unwrap_or_default();
                let level = tags
                    .get(1)
                    .map(|tag| tag.trim_start_matches('@').to_owned())
                    .unwrap_or_default();
                if tags.len() != 2 {
                    report.violations.push(format!(
                        "{suite}: the tag line is exactly `@<ID> @build`, found `{tag_line}`"
                    ));
                }
                current = Some(Scenario {
                    id,
                    level,
                    statement: rest.trim().to_owned(),
                    suite: suite.clone(),
                    steps: Vec::new(),
                    tag_line,
                });
            } else if let Some(scenario) = current.as_mut() {
                for keyword in ["Given ", "When ", "Then ", "And ", "But "] {
                    if let Some(step) = line.strip_prefix(keyword) {
                        scenario.steps.push(format!("{keyword}{step}"));
                        break;
                    }
                }
            }
        }
        if let Some(done) = current.take() {
            report.scenarios.push(done);
        }
    }
    Ok(report)
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
