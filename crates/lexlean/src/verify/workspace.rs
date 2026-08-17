//! Lake workspace preflight (SPEC.md §10.4, §22.2): the recorded workspace
//! files must match the lock and every manifest dependency must be locally
//! available. LexLean never runs `lake update` or fetches dependencies.

use crate::artifact::content_id::Sha256Digest;
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::lock::Lock;
use crate::project::Project;

fn mismatch(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLV7007"), message)
}

/// Check the recorded workspace pins against the current files and the
/// availability of every Lake manifest dependency (VR-17).
pub fn preflight(project: &Project, lock: &Lock) -> Result<(), Diagnostic> {
    let workspace_relative = |name: &str| {
        if project.config.lean_workspace == "." {
            name.to_owned()
        } else {
            format!("{}/{name}", project.config.lean_workspace)
        }
    };
    // The project `lean-toolchain` must carry the exact pinned string
    // (§8.2, §10.4); a hash match against a lock is not enough on its own.
    let toolchain_relative = workspace_relative("lean-toolchain");
    let toolchain_bytes = project
        .confined_file_or_missing(&toolchain_relative, || {
            Diagnostic::new(
                code!("LLV7007"),
                format!("the Lake workspace has no `{toolchain_relative}`"),
            )
        })
        .and_then(|absolute| {
            std::fs::read(absolute.as_std_path()).map_err(|io_error| {
                Diagnostic::new(
                    code!("LLV7001"),
                    format!("{toolchain_relative}: {io_error}"),
                )
            })
        })?;
    let toolchain_text = String::from_utf8_lossy(&toolchain_bytes);
    if toolchain_text.trim() != crate::LEAN_TOOLCHAIN {
        return Err(Diagnostic::new(
            code!("LLV7001"),
            format!(
                "{toolchain_relative} pins `{}`, not the exact language-1.0 toolchain `{}`",
                toolchain_text.trim(),
                crate::LEAN_TOOLCHAIN
            ),
        ));
    }
    for (path, recorded) in &lock.workspace_files {
        // Pinned files are confined: no symlink component (§25.1).
        let absolute = project.confined_file_or_missing(path, || {
            Diagnostic::new(
                code!("LLV7007"),
                format!("the lock records `{path}`, which the Lake workspace does not have"),
            )
        })?;
        let bytes = std::fs::read(absolute.as_std_path())
            .map_err(|io_error| mismatch(format!("{path}: {io_error}")))?;
        let observed = Sha256Digest::of(&bytes);
        if observed != *recorded {
            return Err(mismatch(format!(
                "{path} changed since locking: recorded {}, observed {observed}",
                recorded.to_hex()
            )));
        }
    }

    // Manifest dependencies must be locally available (§10.4). The Lake
    // manifest lists materialized packages under `.lake/packages/<name>`.
    let manifest_relative = workspace_relative("lake-manifest.json");
    let manifest_path = project.absolute(&manifest_relative);
    if std::fs::symlink_metadata(manifest_path.as_std_path()).is_ok() {
        let manifest_path = project.confined_file_or_missing(&manifest_relative, || {
            Diagnostic::new(
                code!("LLV7007"),
                format!("the lock records `{manifest_relative}`, which the Lake workspace does not have"),
            )
        })?;
        let bytes = std::fs::read(manifest_path.as_std_path())
            .map_err(|io_error| mismatch(format!("{manifest_relative}: {io_error}")))?;
        let parsed: serde_json::Value = serde_json::from_slice(&bytes)
            .map_err(|error| mismatch(format!("{manifest_relative}: {error}")))?;
        if let Some(packages) = parsed.get("packages").and_then(|value| value.as_array()) {
            for package in packages {
                let name = package
                    .get("name")
                    .and_then(|value| value.as_str())
                    .unwrap_or("");
                let workspace_root = if project.config.lean_workspace == "." {
                    project.root.clone()
                } else {
                    project.root.join(&project.config.lean_workspace)
                };
                let materialized = workspace_root.join(".lake").join("packages").join(name);
                let path_dir = package
                    .get("dir")
                    .and_then(|value| value.as_str())
                    .map(|dir| workspace_root.join(dir));
                let available = materialized.as_std_path().is_dir()
                    || path_dir.is_some_and(|dir| dir.as_std_path().is_dir());
                if !available {
                    return Err(mismatch(format!(
                        "Lake dependency `{name}` is not locally available; verification never fetches"
                    )));
                }
            }
        }
    }
    Ok(())
}

/// Reject a preexisting workspace module whose full name equals a
/// generated, probe, or audit module (§18.8, §18.9).
pub fn reject_module_conflicts(
    project: &Project,
    module_names: &[String],
) -> Result<(), Diagnostic> {
    let workspace_root = if project.config.lean_workspace == "." {
        project.root.clone()
    } else {
        project.root.join(&project.config.lean_workspace)
    };
    for module in module_names {
        let relative: String = module.replace('.', "/") + ".lean";
        let candidate = workspace_root.join(&relative);
        if candidate.as_std_path().exists() {
            return Err(Diagnostic::new(
                code!("LLV7001"),
                format!(
                    "a preexisting module `{module}` at {} conflicts with a generated module",
                    project.display(&candidate)
                ),
            ));
        }
    }
    Ok(())
}
