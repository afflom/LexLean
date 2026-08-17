//! Separate-process `leanchecker` replay (SPEC.md §22.4): every generated
//! module is replayed and every replay must exit zero. The replay shares
//! Lean's kernel; it is not an independent verifier. Like every Lean
//! process it runs through `lake env` from the pinned toolchain (§22.2)
//! with the generated `.olean` root prepended to `LEAN_PATH`.

use camino::Utf8Path;

use crate::code;
use crate::config::Limits;
use crate::diagnostic::Diagnostic;
use crate::verify::child::{run, ChildHome, ChildRecord, ChildSpec, Normalizer};
use crate::verify::toolchain::Toolchain;

/// Run `lake env <leanchecker> <module>` (the preflighted executable by
/// absolute path) and return its record, whatever the exit status.
pub fn run_leanchecker(
    toolchain: &Toolchain,
    module: &str,
    lean_path: &str,
    workspace: &Utf8Path,
    limits: &Limits,
    normalizer: &Normalizer,
) -> Result<ChildRecord, Diagnostic> {
    let bin_dir = toolchain.root.join("bin");
    run(
        &ChildSpec {
            tool: "leanchecker",
            module: Some(module.to_owned()),
            program: &toolchain.lake.path,
            executable_sha256: toolchain.leanchecker.sha256,
            // The preflighted, digest-checked executable by absolute path,
            // inside the Lake environment (§22.2): `lake env` supplies
            // `LEAN_PATH`, never the executable.
            argv: vec![
                "env".to_owned(),
                toolchain.leanchecker.path.to_string(),
                module.to_owned(),
            ],
            cwd: workspace,
            extra_env: vec![("LEAN_PATH".to_owned(), lean_path.to_owned())],
            home: ChildHome::Toolchain {
                toolchain_bin: &bin_dir,
            },
        },
        limits,
        normalizer,
    )
}

/// Replay one compiled module through `leanchecker`; a nonzero exit is a
/// replay failure (LLV7003).
pub fn replay_module(
    toolchain: &Toolchain,
    module: &str,
    lean_path: &str,
    workspace: &Utf8Path,
    limits: &Limits,
    normalizer: &Normalizer,
) -> Result<ChildRecord, Diagnostic> {
    let record = run_leanchecker(toolchain, module, lean_path, workspace, limits, normalizer)?;
    if record.exit_code != 0 {
        return Err(Diagnostic::new(
            code!("LLV7003"),
            format!(
                "leanchecker replay of `{module}` exited {}: {}{}",
                record.exit_code,
                record.stdout.trim_end(),
                record.stderr.trim_end()
            ),
        ));
    }
    Ok(record)
}
