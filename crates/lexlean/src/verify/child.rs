//! Child process execution and output normalization (SPEC.md §22.3, §22.7,
//! §25.2, §25.4): direct executable and argv invocation with no shell, a
//! deterministic allow-list environment, checked limits, and the exact
//! path-replacement normalization.

use std::io::Read;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use camino::Utf8Path;

use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::Sha256Digest;
use crate::code;
use crate::config::Limits;
use crate::diagnostic::Diagnostic;

/// The §22.7 normalizer: ordered longest-prefix replacements.
#[derive(Debug, Clone, Default)]
pub struct Normalizer {
    replacements: Vec<(String, &'static str)>,
}

impl Normalizer {
    /// Build the ordered replacement list: staging, project, Lake
    /// workspace, toolchain, home.
    #[must_use]
    pub fn new(
        staging: &Utf8Path,
        project: &Utf8Path,
        lake_workspace: &Utf8Path,
        toolchain: &Utf8Path,
    ) -> Self {
        let mut replacements = vec![
            (staging.to_string(), "$STAGING"),
            (project.to_string(), "$PROJECT"),
            (lake_workspace.to_string(), "$LAKE_WORKSPACE"),
            (toolchain.to_string(), "$TOOLCHAIN"),
        ];
        if let Some(home) = std::env::var_os("HOME") {
            if let Some(text) = home.to_str() {
                replacements.push((text.to_owned(), "$HOME"));
            }
        }
        Self { replacements }
    }

    /// Normalize process output (§22.7): CRLF and CR to LF, ANSI escapes
    /// removed, prefixes replaced in order, trailing spaces removed, blank
    /// final lines collapsed to one final LF.
    #[must_use]
    pub fn normalize(&self, bytes: &[u8]) -> String {
        let raw = String::from_utf8_lossy(bytes);
        // 1. Line endings.
        let mut text = String::with_capacity(raw.len());
        let mut chars = raw.chars().peekable();
        while let Some(c) = chars.next() {
            if c == '\r' {
                if chars.peek() == Some(&'\n') {
                    chars.next();
                }
                text.push('\n');
            } else {
                text.push(c);
            }
        }
        // 2. ANSI escape sequences.
        let mut stripped = String::with_capacity(text.len());
        let mut iterator = text.chars().peekable();
        while let Some(c) = iterator.next() {
            if c == '\u{1b}' {
                if iterator.peek() == Some(&'[') {
                    iterator.next();
                    for follow in iterator.by_ref() {
                        if follow.is_ascii_alphabetic() {
                            break;
                        }
                    }
                }
                continue;
            }
            stripped.push(c);
        }
        // 3. Ordered prefix replacement.
        let mut replaced = stripped;
        for (prefix, token) in &self.replacements {
            if !prefix.is_empty() {
                replaced = replaced.replace(prefix, token);
            }
        }
        // 4–5. Trailing spaces; blank final lines collapse to one LF.
        let mut lines: Vec<&str> = replaced.split('\n').map(str::trim_end).collect();
        while lines.last() == Some(&"") {
            lines.pop();
        }
        let mut result = lines.join("\n");
        result.push('\n');
        result
    }

    /// Normalize one argv element for records.
    #[must_use]
    pub fn normalize_arg(&self, argument: &str) -> String {
        let mut out = argument.to_owned();
        for (prefix, token) in &self.replacements {
            if !prefix.is_empty() {
                out = out.replace(prefix, token);
            }
        }
        out
    }

    /// Does normalized output still contain an unexpected absolute path
    /// (§22.7)? Successful output carrying one fails attestation
    /// construction.
    #[must_use]
    pub fn has_unexpected_absolute_path(&self, text: &str) -> bool {
        for marker in ["/home/", "/Users/", "/tmp/", "/workspaces/"] {
            if text.contains(marker) {
                return true;
            }
        }
        false
    }
}

/// One recorded child process (§22.3).
#[derive(Debug, Clone)]
pub struct ChildRecord {
    /// The tool name.
    pub tool: String,
    /// The module this run concerned, when per-module.
    pub module: Option<String>,
    /// The normalized argv.
    pub argv: Vec<String>,
    /// The exit code.
    pub exit_code: i32,
    /// Normalized stdout.
    pub stdout: String,
    /// Normalized stderr.
    pub stderr: String,
    /// SHA-256 of the executable.
    pub executable_sha256: Sha256Digest,
}

impl ChildRecord {
    /// The canonical JSON process record.
    #[must_use]
    pub fn to_json(&self) -> Json {
        let mut fields = vec![
            ("tool", Json::Str(self.tool.clone())),
            (
                "argv",
                Json::Arr(self.argv.iter().cloned().map(Json::Str).collect()),
            ),
            ("exit_code", Json::Int(i64::from(self.exit_code))),
            (
                "executable_sha256",
                Json::Str(self.executable_sha256.to_hex()),
            ),
            ("stdout", Json::Str(self.stdout.clone())),
            ("stderr", Json::Str(self.stderr.clone())),
            (
                "stdout_sha256",
                Json::Str(Sha256Digest::of(self.stdout.as_bytes()).to_hex()),
            ),
            (
                "stderr_sha256",
                Json::Str(Sha256Digest::of(self.stderr.as_bytes()).to_hex()),
            ),
        ];
        if let Some(module) = &self.module {
            fields.push(("module", Json::Str(module.clone())));
        }
        Json::object(fields)
    }
}

/// One child invocation.
pub struct ChildSpec<'a> {
    /// The tool label for records.
    pub tool: &'a str,
    /// The module label, when per-module.
    pub module: Option<String>,
    /// The absolute executable.
    pub program: &'a Utf8Path,
    /// The executable digest, already computed by preflight.
    pub executable_sha256: Sha256Digest,
    /// The argument vector.
    pub argv: Vec<String>,
    /// The working directory (the Lake workspace, §22.2).
    pub cwd: &'a Utf8Path,
    /// Extra environment rows (`LEAN_PATH` and friends).
    pub extra_env: Vec<(String, String)>,
    /// The toolchain bin directory, prepended to `PATH`.
    pub toolchain_bin: &'a Utf8Path,
}

/// Run one child under the allow-list environment (§25.4), the timeout,
/// and the output cap (§25.5).
pub fn run(
    spec: &ChildSpec<'_>,
    limits: &Limits,
    normalizer: &Normalizer,
) -> Result<ChildRecord, Diagnostic> {
    let existing_path = std::env::var("PATH").unwrap_or_default();
    let mut command = Command::new(spec.program.as_std_path());
    command
        .args(&spec.argv)
        .current_dir(spec.cwd.as_std_path())
        .env_clear()
        .env("PATH", format!("{}:{existing_path}", spec.toolchain_bin))
        .env(
            "HOME",
            std::env::var_os("HOME").unwrap_or_else(|| "/".into()),
        )
        .env("NO_COLOR", "1")
        .env("LANG", "C.UTF-8")
        .env("LC_ALL", "C.UTF-8")
        .env("GIT_TERMINAL_PROMPT", "0")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(elan_home) = std::env::var_os("ELAN_HOME") {
        command.env("ELAN_HOME", elan_home);
    }
    for (key, value) in &spec.extra_env {
        command.env(key, value);
    }
    let mut child = command.spawn().map_err(|io_error| {
        Diagnostic::new(code!("LLV7001"), format!("{}: {io_error}", spec.program))
    })?;
    let cap = usize::try_from(limits.max_child_output_bytes).unwrap_or(usize::MAX);
    let mut stdout_pipe = child.stdout.take().expect("stdout piped");
    let mut stderr_pipe = child.stderr.take().expect("stderr piped");
    let stdout_reader = std::thread::spawn(move || {
        let mut buffer = Vec::new();
        let _ = stdout_pipe
            .by_ref()
            .take(cap as u64 + 1)
            .read_to_end(&mut buffer);
        buffer
    });
    let stderr_reader = std::thread::spawn(move || {
        let mut buffer = Vec::new();
        let _ = stderr_pipe
            .by_ref()
            .take(cap as u64 + 1)
            .read_to_end(&mut buffer);
        buffer
    });
    let deadline = Instant::now() + Duration::from_millis(limits.child_timeout_ms);
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(Diagnostic::new(
                        code!("LLS8002"),
                        format!(
                            "child_timeout_ms exceeded: configured {}",
                            limits.child_timeout_ms
                        ),
                    ));
                }
                std::thread::sleep(Duration::from_millis(10));
            }
            Err(io_error) => {
                return Err(Diagnostic::new(
                    code!("LLV7001"),
                    format!("waiting for {}: {io_error}", spec.program),
                ));
            }
        }
    };
    let stdout_bytes = stdout_reader.join().unwrap_or_default();
    let stderr_bytes = stderr_reader.join().unwrap_or_default();
    if stdout_bytes.len() > cap || stderr_bytes.len() > cap {
        return Err(Diagnostic::new(
            code!("LLS8002"),
            format!(
                "max_child_output_bytes exceeded: configured {}",
                limits.max_child_output_bytes
            ),
        ));
    }
    Ok(ChildRecord {
        tool: spec.tool.to_owned(),
        module: spec.module.clone(),
        argv: spec
            .argv
            .iter()
            .map(|argument| normalizer.normalize_arg(argument))
            .collect(),
        exit_code: status.code().unwrap_or(-1),
        stdout: normalizer.normalize(&stdout_bytes),
        stderr: normalizer.normalize(&stderr_bytes),
        executable_sha256: spec.executable_sha256,
    })
}
