//! The model gate (SPEC.md §27.5): parse the model, regenerate the
//! generated documents in memory, compare exact bytes, scan feature
//! scenarios and test names, run the honesty vocabulary checks, and run the
//! repository audits.

use std::path::{Path, PathBuf};

use repo_model::{codegen, Model};

use crate::Fail;

/// R1, §27.5: the generated documents equal the model, byte for byte.
pub fn check_model(root: &Path, write: bool) -> Result<(), Fail> {
    let model = Model::load(&root.join("model"))?;
    model.check()?;

    let conformance = codegen::render_conformance(&model);
    let errors = codegen::render_errors(&model);
    let conformance_path: PathBuf = root.join(codegen::CONFORMANCE_PATH);
    let errors_path: PathBuf = root.join(codegen::ERRORS_PATH);

    if write {
        std::fs::write(&conformance_path, &conformance)?;
        std::fs::write(&errors_path, &errors)?;
        println!(
            "wrote {} and {}",
            conformance_path.display(),
            errors_path.display()
        );
        return Ok(());
    }
    for (path, generated) in [(&conformance_path, &conformance), (&errors_path, &errors)] {
        let committed = std::fs::read_to_string(path)
            .map_err(|error| format!("{}: {error}\nrun `just model-write`", path.display()))?;
        if committed != **generated {
            return Err(format!(
                "{} is stale: it disagrees with model/*.toml (R1). Run `just model-write`.",
                path.display()
            )
            .into());
        }
    }

    // §27.5 steps 5–7: feature scenarios, Rust test names, and the honesty
    // vocabulary, through the same meta-gate `just bdd` runs.
    let tests = repo_conformance::workspace_test_names(root);
    let report = repo_conformance::check_honesty(root, &tests)?;
    if !report.is_clean() {
        return Err(format!(
            "the honesty meta-gate failed inside validate-model:\n\n{}",
            report.violations.join("\n\n")
        )
        .into());
    }

    // §27.5 step 8: the repository audits.
    crate::audit::audit_deferral(root)?;
    crate::audit::audit_errors(root, &model)?;
    crate::audit::audit_shipped(root)?;
    crate::audit::audit_generated(root)?;
    crate::audit::audit_language_closure(root)?;
    crate::audit::audit_no_unsafe(root)?;
    crate::audit::audit_surface_disjointness(root)?;
    crate::audit::audit_atlas_library(root)?;

    println!(
        "validate-model: documents current, {} ids, {} codes, meta-gate and audits clean (R1)",
        model.ids.id.len(),
        model.errors.error.len()
    );
    Ok(())
}
