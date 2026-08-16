//! Toolchain preflight (SPEC.md §8.2, §22.2): locate the pinned Lean
//! toolchain, require the exact reported version, and record executable
//! digests.

use camino::Utf8PathBuf;

use crate::artifact::content_id::Sha256Digest;
use crate::code;
use crate::diagnostic::Diagnostic;

/// One preflighted tool.
#[derive(Debug, Clone)]
pub struct Tool {
    /// The absolute executable path.
    pub path: Utf8PathBuf,
    /// SHA-256 of the executable bytes.
    pub sha256: Sha256Digest,
    /// The recorded, normalized version output.
    pub version_output: String,
}

/// The pinned toolchain.
#[derive(Debug, Clone)]
pub struct Toolchain {
    /// The toolchain root directory.
    pub root: Utf8PathBuf,
    /// `lean`.
    pub lean: Tool,
    /// `lake`.
    pub lake: Tool,
    /// `leanchecker`.
    pub leanchecker: Tool,
}

fn environment(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLV7001"), message)
}

/// The elan toolchain directory for the pinned toolchain string: `/` maps
/// to `--` and `:` to `---` under `$ELAN_HOME/toolchains` or
/// `$HOME/.elan/toolchains`.
pub fn toolchain_root() -> Result<Utf8PathBuf, Diagnostic> {
    let elan_home = std::env::var_os("ELAN_HOME")
        .map(std::path::PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| std::path::PathBuf::from(home).join(".elan"))
        })
        .ok_or_else(|| environment("neither ELAN_HOME nor HOME is set"))?;
    let mangled = crate::LEAN_TOOLCHAIN.replace('/', "--").replace(':', "---");
    let root = elan_home.join("toolchains").join(mangled);
    Utf8PathBuf::from_path_buf(root)
        .map_err(|bad| environment(format!("non-UTF-8 toolchain path: {}", bad.display())))
}

fn probe(path: &Utf8PathBuf, argv: &[&str], bin_dir: &Utf8PathBuf) -> Result<String, Diagnostic> {
    let existing_path = std::env::var("PATH").unwrap_or_default();
    let output = std::process::Command::new(path.as_std_path())
        .args(argv)
        .env_clear()
        .env("PATH", format!("{bin_dir}:{existing_path}"))
        .env(
            "HOME",
            std::env::var_os("HOME").unwrap_or_else(|| "/".into()),
        )
        .env("NO_COLOR", "1")
        .env("LANG", "C.UTF-8")
        .env("LC_ALL", "C.UTF-8")
        .env("GIT_TERMINAL_PROMPT", "0")
        .output()
        .map_err(|io_error| environment(format!("{path}: {io_error}")))?;
    let mut text = String::from_utf8_lossy(&output.stdout).into_owned();
    if text.trim().is_empty() {
        text = String::from_utf8_lossy(&output.stderr).into_owned();
    }
    Ok(text.replace("\r\n", "\n").trim_end().to_owned())
}

fn load_tool(
    bin_dir: &Utf8PathBuf,
    name: &str,
    version_argv: Option<&[&str]>,
) -> Result<Tool, Diagnostic> {
    let path = bin_dir.join(name);
    let bytes = std::fs::read(path.as_std_path()).map_err(|io_error| {
        environment(format!(
            "the pinned toolchain has no `{name}` executable: {path}: {io_error}"
        ))
    })?;
    let sha256 = Sha256Digest::of(&bytes);
    let version_output = match version_argv {
        Some(argv) => probe(&path, argv, bin_dir)?,
        None => String::new(),
    };
    Ok(Tool {
        path,
        sha256,
        version_output,
    })
}

/// Locate and preflight the pinned toolchain: `lean` and `lake` must report
/// version 4.32.1 (§8.2); every executable digest is recorded (§22.9).
pub fn preflight() -> Result<Toolchain, Diagnostic> {
    let root = toolchain_root()?;
    let bin_dir = root.join("bin");
    if !bin_dir.as_std_path().is_dir() {
        return Err(environment(format!(
            "the pinned toolchain `{}` is not installed at {root}",
            crate::LEAN_TOOLCHAIN
        )));
    }
    let lean = load_tool(&bin_dir, "lean", Some(&["--version"]))?;
    if !lean.version_output.contains(crate::LEAN_VERSION) {
        return Err(environment(format!(
            "lean reports `{}`, not version {}",
            lean.version_output,
            crate::LEAN_VERSION
        )));
    }
    let lake = load_tool(&bin_dir, "lake", Some(&["--version"]))?;
    if !lake.version_output.contains(crate::LEAN_VERSION) {
        return Err(environment(format!(
            "lake reports `{}`, not Lean version {}",
            lake.version_output,
            crate::LEAN_VERSION
        )));
    }
    // `leanchecker` takes no version flag; its digest and recorded output
    // come from the replay runs themselves (§22.4).
    let leanchecker = load_tool(&bin_dir, "leanchecker", None)?;
    Ok(Toolchain {
        root,
        lean,
        lake,
        leanchecker,
    })
}
