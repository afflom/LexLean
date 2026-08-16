//! Child process execution and output normalization (SPEC.md §22.3, §22.7,
//! §25.2, §25.4): direct executable and argv invocation with no shell, a
//! deterministic allow-list environment, checked limits, and the exact
//! path-replacement normalization.

use std::io::Read;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use camino::{Utf8Path, Utf8PathBuf};

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
    /// (§22.7)? After the ordered prefix replacement, every remaining
    /// `/`-rooted path (`/` at a token boundary followed by a path segment)
    /// or drive-rooted Windows path (`X:\` or `X:/` at a token boundary)
    /// is unexpected. `$PLACEHOLDER`-prefixed forms and URL schemes
    /// (`scheme://host`) are not rooted paths. Successful output carrying
    /// one fails attestation construction.
    #[must_use]
    pub fn has_unexpected_absolute_path(&self, text: &str) -> bool {
        first_unexpected_absolute_path(text).is_some()
    }
}

/// A character that can begin a path segment after the root separator.
fn starts_segment(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '.'
}

/// A character that separates tokens, so a following `/` starts a rooted
/// path rather than continuing one.
fn is_token_boundary(c: char) -> bool {
    c.is_whitespace()
        || matches!(
            c,
            '"' | '\'' | '`' | '(' | '[' | '{' | '<' | ',' | ';' | '='
        )
}

/// The first unexpected absolute path in normalized text, when any: the
/// byte offset and the offending token.
#[must_use]
pub fn first_unexpected_absolute_path(text: &str) -> Option<(usize, String)> {
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    for (index, &(offset, c)) in chars.iter().enumerate() {
        let previous = index.checked_sub(1).map(|i| chars[i].1);
        let at_boundary = previous.is_none_or(is_token_boundary);
        let next = chars.get(index.saturating_add(1)).map(|pair| pair.1);
        let rooted_posix = c == '/' && at_boundary && next.is_some_and(starts_segment);
        let rooted_windows = c.is_ascii_alphabetic()
            && at_boundary
            && next == Some(':')
            && chars
                .get(index.saturating_add(2))
                .is_some_and(|pair| pair.1 == '/' || pair.1 == '\\')
            && chars
                .get(index.saturating_add(3))
                .is_some_and(|pair| starts_segment(pair.1));
        if rooted_posix || rooted_windows {
            let token: String = text[offset..]
                .chars()
                .take_while(|c| {
                    !c.is_whitespace()
                        && !matches!(c, '"' | '\'' | '`' | ')' | ']' | '}' | '>' | ',' | ';')
                })
                .collect();
            return Some((offset, token));
        }
    }
    None
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

/// Locate an executable by name on the current `PATH` (§25.2): the
/// resolution is explicit and recorded, never left to the child.
pub fn resolve_on_path(name: &str) -> Result<Utf8PathBuf, Diagnostic> {
    let path_value = std::env::var_os("PATH").unwrap_or_default();
    for directory in std::env::split_paths(&path_value) {
        if directory.as_os_str().is_empty() {
            continue;
        }
        let candidate = directory.join(name);
        let Ok(metadata) = std::fs::metadata(&candidate) else {
            continue;
        };
        if !metadata.is_file() {
            continue;
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if metadata.permissions().mode() & 0o111 == 0 {
                continue;
            }
        }
        return Utf8PathBuf::from_path_buf(candidate).map_err(|bad| {
            Diagnostic::new(
                code!("LLV7008"),
                format!(
                    "non-UTF-8 path in the environment: {}",
                    bad.to_string_lossy()
                ),
            )
        });
    }
    Err(Diagnostic::new(
        code!("LLV7001"),
        format!("no `{name}` executable is available on PATH"),
    ))
}

/// Run one child under the allow-list environment (§25.4), the timeout,
/// and the output cap (§25.5). Every arithmetic step over the configured
/// limits is checked; a limit failure is `LLS8002` naming the limit, the
/// configured value, the observed value, and the tool.
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
        Diagnostic::new(
            code!("LLV7001"),
            format!("{}: cannot start `{}`: {io_error}", spec.tool, spec.program),
        )
    })?;
    let cap = limits.max_child_output_bytes;
    // Read one byte past the cap so an overflow is observed as `> cap`
    // without ever buffering unbounded output.
    let read_limit = cap.saturating_add(1);
    let (Some(mut stdout_pipe), Some(mut stderr_pipe)) = (child.stdout.take(), child.stderr.take())
    else {
        let _ = child.kill();
        let _ = child.wait();
        return Err(Diagnostic::new(
            code!("LLI9001"),
            format!("{}: the child pipes were not attached", spec.tool),
        ));
    };
    let stdout_reader = std::thread::spawn(move || {
        let mut buffer = Vec::new();
        let _ = stdout_pipe
            .by_ref()
            .take(read_limit)
            .read_to_end(&mut buffer);
        buffer
    });
    let stderr_reader = std::thread::spawn(move || {
        let mut buffer = Vec::new();
        let _ = stderr_pipe
            .by_ref()
            .take(read_limit)
            .read_to_end(&mut buffer);
        buffer
    });
    let started = Instant::now();
    let timeout = Duration::from_millis(limits.child_timeout_ms);
    let deadline = started.checked_add(timeout);
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {
                let now = Instant::now();
                if deadline.is_none_or(|deadline| now >= deadline) {
                    let _ = child.kill();
                    let _ = child.wait();
                    let elapsed_ms = now.saturating_duration_since(started).as_millis();
                    return Err(Diagnostic::new(
                        code!("LLS8002"),
                        format!(
                            "child_timeout_ms exceeded by `{}` in phase {}: configured {}, observed {} ms",
                            spec.tool,
                            spec.module.as_deref().unwrap_or("verify"),
                            limits.child_timeout_ms,
                            elapsed_ms
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
    let stdout_len = u64::try_from(stdout_bytes.len()).unwrap_or(u64::MAX);
    let stderr_len = u64::try_from(stderr_bytes.len()).unwrap_or(u64::MAX);
    if stdout_len > cap || stderr_len > cap {
        let (stream, observed) = if stdout_len > cap {
            ("stdout", stdout_len)
        } else {
            ("stderr", stderr_len)
        };
        return Err(Diagnostic::new(
            code!("LLS8002"),
            format!(
                "max_child_output_bytes exceeded by `{}` on {stream} in phase {}: configured {}, observed at least {observed} bytes",
                spec.tool,
                spec.module.as_deref().unwrap_or("verify"),
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
