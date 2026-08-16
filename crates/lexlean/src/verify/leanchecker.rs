//! Separate-process `leanchecker` replay (SPEC.md §22.4): every generated
//! module is replayed and every replay must exit zero. The replay shares
//! Lean's kernel; it is not an independent verifier.

use camino::Utf8Path;

use crate::code;
use crate::config::Limits;
use crate::diagnostic::Diagnostic;
use crate::verify::child::{run, ChildRecord, ChildSpec, Normalizer};
use crate::verify::toolchain::Toolchain;

/// Replay one compiled module through `leanchecker`.
pub fn replay_module(
    toolchain: &Toolchain,
    module: &str,
    lean_path: &str,
    workspace: &Utf8Path,
    limits: &Limits,
    normalizer: &Normalizer,
) -> Result<ChildRecord, Diagnostic> {
    let bin_dir = toolchain.root.join("bin");
    let record = run(
        &ChildSpec {
            tool: "leanchecker",
            module: Some(module.to_owned()),
            program: &toolchain.leanchecker.path,
            executable_sha256: toolchain.leanchecker.sha256,
            argv: vec![module.to_owned()],
            cwd: workspace,
            extra_env: vec![("LEAN_PATH".to_owned(), lean_path.to_owned())],
            toolchain_bin: &bin_dir,
        },
        limits,
        normalizer,
    )?;
    if record.exit_code != 0 {
        return Err(Diagnostic::new(
            code!("LLV7003"),
            format!(
                "leanchecker replay of `{module}` exited {}: {}",
                record.exit_code,
                record.stderr.trim_end()
            ),
        ));
    }
    Ok(record)
}
