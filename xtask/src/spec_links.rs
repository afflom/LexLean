//! The specification-link gate (SPEC.md §27.6, RP-07): the §31 table and
//! `model/ids.toml` are bijective and text-consistent, every ID is `build`,
//! and every referenced source section exists.

use std::collections::BTreeSet;
use std::path::Path;

use repo_model::Model;

use crate::Fail;

struct TableRow {
    id: String,
    suite: String,
    statement: String,
    sections: Vec<String>,
}

fn parse_table(spec: &str) -> Result<Vec<TableRow>, Fail> {
    let registry = spec
        .split("## 31. Complete conformance-ID registry")
        .nth(1)
        .ok_or("SPEC.md has no §31 registry")?
        .split("## 32.")
        .next()
        .ok_or("SPEC.md has no §32 after the registry")?;
    let mut rows = Vec::new();
    for line in registry.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with("| `") {
            continue;
        }
        let cells: Vec<&str> = trimmed
            .trim_matches('|')
            .split('|')
            .map(str::trim)
            .collect();
        if cells.len() != 4 {
            continue;
        }
        let strip_ticks = |cell: &str| cell.trim_matches('`').to_owned();
        let id = strip_ticks(cells[0]);
        if id.len() != 5 || !id.as_bytes()[..2].iter().all(u8::is_ascii_uppercase) {
            continue;
        }
        let sections = cells[3]
            .split(',')
            .map(|reference| reference.trim().trim_start_matches('§').to_owned())
            .collect();
        rows.push(TableRow {
            id,
            suite: strip_ticks(cells[1]),
            statement: cells[2].to_owned(),
            sections,
        });
    }
    Ok(rows)
}

/// Run the gate.
pub fn validate(root: &Path) -> Result<(), Fail> {
    let spec = std::fs::read_to_string(root.join("SPEC.md"))?;
    let rows = parse_table(&spec)?;
    if rows.len() != 211 {
        return Err(format!("RP-07: the §31 table has {} rows, not 211", rows.len()).into());
    }
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for row in &rows {
        if !seen.insert(&row.id) {
            return Err(format!("RP-07: `{}` appears twice in the §31 table", row.id).into());
        }
    }

    let model = Model::load(&root.join("model"))?;
    let register: BTreeSet<&str> = model.ids.id.iter().map(|row| row.id.as_str()).collect();
    for row in &rows {
        let Some(model_row) = model.ids.get(&row.id) else {
            return Err(format!(
                "RP-07: `{}` is in the §31 table but not in model/ids.toml",
                row.id
            )
            .into());
        };
        if model_row.suite != row.suite {
            return Err(format!(
                "RP-07: `{}` has suite `{}` in the table and `{}` in the register",
                row.id, row.suite, model_row.suite
            )
            .into());
        }
        if model_row.statement != row.statement {
            return Err(format!(
                "RP-07: `{}`'s statement differs between the table and the register:\n  table:    {}\n  register: {}",
                row.id, row.statement, model_row.statement
            )
            .into());
        }
        if model_row.level.as_str() != "build" {
            return Err(format!(
                "RP-07: `{}` must be `build`, found `{}` (§27.3)",
                row.id,
                model_row.level.as_str()
            )
            .into());
        }
    }
    for model_row in &model.ids.id {
        if !seen.contains(model_row.id.as_str()) {
            return Err(format!(
                "RP-07: `{}` is registered but absent from the §31 table",
                model_row.id
            )
            .into());
        }
    }
    let _ = register;

    // Every source section referenced by an ID exists.
    for row in &rows {
        for section in &row.sections {
            let normalized = section
                .split_whitespace()
                .next()
                .unwrap_or(section)
                .to_owned();
            let exists = if normalized.contains('.') {
                spec.contains(&format!("### {normalized} "))
                    || spec.contains(&format!("### {normalized}\n"))
            } else {
                spec.contains(&format!("## {normalized}. "))
            };
            if !exists {
                return Err(format!(
                    "RP-07: `{}` references §{normalized}, which does not exist",
                    row.id
                )
                .into());
            }
        }
    }
    // Derived, not written down: a literal here would keep reporting the old
    // count after the register grew, which is the failure this gate exists to
    // catch in the documents it checks.
    println!(
        "validate-spec-links: {} table rows bijective with the register (RP-07)",
        rows.len()
    );
    Ok(())
}
