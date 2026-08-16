//! The external PDF provider protocol (SPEC.md §19.7, §19.8): optional,
//! isolated, hash-checked, and with no proof authority whatsoever.
//!
//! Fixed protocol decisions:
//!
//! - the configured `output` is a bare file name (no `/`, `\`, or `..`
//!   segment) so the provider can only ever satisfy the protocol inside
//!   `{out_dir}`;
//! - declared resources are staged by basename next to the canonical
//!   `.tex`; two resources with one basename, or a resource whose basename
//!   is the `.tex` itself, are configuration conflicts (LLB6004);
//! - the produced PDF is capped by `max_child_output_bytes` — the provider
//!   is a child process and its file output is child output, so the same
//!   configured limit governs it (LLS8002);
//! - after compilation `{out_dir}` must contain exactly the configured
//!   output regular file; every extra entry is named in the failure.

use std::io::Read;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use camino::Utf8PathBuf;

use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::{pdf_recipe_id, Sha256Digest};
use crate::code;
use crate::config::{Limits, PdfProvider};
use crate::diagnostic::Diagnostic;
use crate::project::Project;

/// One recorded provider process.
#[derive(Debug, Clone)]
pub struct PdfProcess {
    /// The argv as configured, placeholders unexpanded for the version
    /// probe and expanded for the compile step.
    pub argv: Vec<String>,
    /// The exit code.
    pub exit_code: i32,
    /// Normalized stdout.
    pub stdout: String,
    /// Normalized stderr.
    pub stderr: String,
    /// SHA-256 of the executable bytes.
    pub executable_sha256: Sha256Digest,
}

impl PdfProcess {
    /// The attestation process record (tool `pdf`), argv normalized.
    #[must_use]
    pub fn to_child_record(
        &self,
        module: &str,
        normalizer: &crate::verify::child::Normalizer,
    ) -> crate::verify::child::ChildRecord {
        crate::verify::child::ChildRecord {
            tool: "pdf".to_owned(),
            module: Some(module.to_owned()),
            argv: self
                .argv
                .iter()
                .map(|argument| normalizer.normalize_arg(argument))
                .collect(),
            exit_code: self.exit_code,
            stdout: normalizer.normalize(self.stdout.as_bytes()),
            stderr: normalizer.normalize(self.stderr.as_bytes()),
            executable_sha256: self.executable_sha256,
        }
    }
}

/// Is a configured output pattern a bare file name?
#[must_use]
pub fn is_bare_file_name(name: &str) -> bool {
    !name.is_empty()
        && !name.contains('/')
        && !name.contains('\\')
        && name != "."
        && name != ".."
        && !name.contains('\0')
}

/// The outcome of one provider run.
#[derive(Debug)]
pub struct PdfResult {
    /// The §19.8 recipe ID.
    pub recipe_id: Sha256Digest,
    /// The produced PDF bytes.
    pub pdf_bytes: Vec<u8>,
    /// SHA-256 of the PDF bytes.
    pub pdf_sha256: Sha256Digest,
    /// The version probe record.
    pub version: PdfProcess,
    /// The compile record.
    pub compile: PdfProcess,
}

fn protocol(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLB6004"), message)
}

fn policy(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLS8004"), message)
}

fn normalize_output(bytes: &[u8]) -> String {
    let text = String::from_utf8_lossy(bytes);
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\r' {
            if chars.peek() == Some(&'\n') {
                chars.next();
            }
            out.push('\n');
        } else {
            out.push(c);
        }
    }
    let mut lines: Vec<&str> = out.split('\n').map(str::trim_end).collect();
    while lines.last() == Some(&"") {
        lines.pop();
    }
    let mut result = lines.join("\n");
    result.push('\n');
    result
}

/// Run one child with the isolated environment (§25.4): a temporary home,
/// no inherited proxy variables, and no shell (§25.2). Enforces the child
/// timeout and output caps with checked arithmetic (§25.5).
fn run_child(
    program: &Utf8PathBuf,
    argv: &[String],
    workdir: &std::path::Path,
    home: &std::path::Path,
    limits: &Limits,
    executable_sha256: Sha256Digest,
) -> Result<PdfProcess, Diagnostic> {
    let path_var = std::env::var_os("PATH").unwrap_or_default();
    let mut child = Command::new(program.as_std_path())
        .args(argv)
        .current_dir(workdir)
        .env_clear()
        .env("PATH", path_var)
        .env("HOME", home)
        .env("NO_COLOR", "1")
        .env("LANG", "C.UTF-8")
        .env("LC_ALL", "C.UTF-8")
        .env("GIT_TERMINAL_PROMPT", "0")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|io_error| protocol(format!("{program}: {io_error}")))?;

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
            Err(io_error) => return Err(protocol(format!("waiting for {program}: {io_error}"))),
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
    Ok(PdfProcess {
        argv: argv.to_vec(),
        exit_code: status.code().unwrap_or(-1),
        stdout: normalize_output(&stdout_bytes),
        stderr: normalize_output(&stderr_bytes),
        executable_sha256,
    })
}

/// Run the configured provider for one canonical `.tex` (§19.7).
#[allow(clippy::too_many_lines)]
pub fn run_provider(
    project: &Project,
    provider: &PdfProvider,
    tex_bytes: &[u8],
    stem: &str,
    staging_parent: &Utf8PathBuf,
) -> Result<PdfResult, Diagnostic> {
    let limits = &project.config.limits;

    // 1. Verify the provider executable SHA-256 (§19.7 step 1, SE-08).
    let program_path = project.confined_file(&provider.program)?;
    let program_bytes = std::fs::read(program_path.as_std_path())
        .map_err(|io_error| protocol(format!("{}: {io_error}", provider.program)))?;
    let program_sha256 = Sha256Digest::of(&program_bytes);
    if program_sha256 != provider.program_sha256 {
        return Err(policy(format!(
            "pdf program hash mismatch: configured {}, observed {program_sha256}",
            provider.program_sha256.to_hex()
        )));
    }

    // 4–5. An isolated temporary working directory holding exactly the
    // canonical `.tex` and the declared regular resources.
    let workspace = tempfile::tempdir_in(staging_parent.as_std_path())
        .map_err(|io_error| protocol(format!("pdf staging: {io_error}")))?;
    let workdir = workspace.path().join("work");
    let out_dir = workspace.path().join("out");
    let home = workspace.path().join("home");
    for directory in [&workdir, &out_dir, &home] {
        std::fs::create_dir_all(directory)
            .map_err(|io_error| protocol(format!("pdf staging: {io_error}")))?;
    }
    let tex_name = format!("{stem}.tex");
    if !is_bare_file_name(&provider.output) {
        return Err(protocol(format!(
            "pdf output `{}` is not a bare file name",
            provider.output
        )));
    }
    let output_name = provider.output.replace("{stem}", stem);
    if !is_bare_file_name(&output_name) {
        return Err(protocol(format!(
            "pdf output `{output_name}` is not a bare file name"
        )));
    }
    std::fs::write(workdir.join(&tex_name), tex_bytes)
        .map_err(|io_error| protocol(format!("pdf staging: {io_error}")))?;
    let mut resource_rows: Vec<(String, Sha256Digest)> = Vec::new();
    let mut staged_names: std::collections::BTreeMap<String, String> =
        std::collections::BTreeMap::new();
    staged_names.insert(tex_name.clone(), "the canonical document".to_owned());
    for resource in &provider.resources {
        let absolute = project.confined_file(resource)?;
        let bytes = std::fs::read(absolute.as_std_path())
            .map_err(|io_error| protocol(format!("{resource}: {io_error}")))?;
        let name = resource.rsplit('/').next().unwrap_or(resource);
        if let Some(previous) = staged_names.insert(name.to_owned(), resource.clone()) {
            return Err(protocol(format!(
                "pdf resource `{resource}` collides with {previous} at the staged name `{name}`"
            )));
        }
        std::fs::write(workdir.join(name), &bytes)
            .map_err(|io_error| protocol(format!("pdf staging: {io_error}")))?;
        resource_rows.push((resource.clone(), Sha256Digest::of(&bytes)));
    }
    resource_rows.sort_by(|a, b| a.0.cmp(&b.0));

    // 2–3. The version probe with no shell, stdout normalized and checked.
    let version = run_child(
        &program_path,
        &provider.version_argv,
        &workdir,
        &home,
        limits,
        program_sha256,
    )?;
    let observed_version = Sha256Digest::of(version.stdout.as_bytes());
    if observed_version != provider.version_stdout_sha256 {
        return Err(policy(format!(
            "pdf version output hash mismatch: configured {}, observed {observed_version}",
            provider.version_stdout_sha256.to_hex()
        )));
    }

    // 6–7. Whole-argument placeholder expansion, then direct invocation.
    let expanded: Vec<String> = provider
        .compile_argv
        .iter()
        .map(|argument| match argument.as_str() {
            "{input}" => tex_name.clone(),
            "{out_dir}" => out_dir.to_string_lossy().into_owned(),
            "{stem}" => stem.to_owned(),
            other => other.to_owned(),
        })
        .collect();
    let compile = run_child(
        &program_path,
        &expanded,
        &workdir,
        &home,
        limits,
        program_sha256,
    )?;
    if compile.exit_code != 0 {
        return Err(protocol(format!(
            "pdf provider exited {}: {}",
            compile.exit_code,
            compile.stderr.trim_end()
        )));
    }

    // 9–10. Exactly the configured output regular file, beginning `%PDF-`,
    // within the child output cap; nothing else in the output directory.
    let mut extras: Vec<String> = Vec::new();
    for entry in std::fs::read_dir(&out_dir)
        .map_err(|io_error| protocol(format!("pdf output directory: {io_error}")))?
    {
        let entry =
            entry.map_err(|io_error| protocol(format!("pdf output directory: {io_error}")))?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if name != output_name {
            extras.push(name);
        }
    }
    if !extras.is_empty() {
        extras.sort();
        return Err(protocol(format!(
            "the provider left entries other than `{output_name}` in the output directory: {}",
            extras.join(", ")
        )));
    }
    let output_path = out_dir.join(&output_name);
    let metadata = std::fs::symlink_metadata(&output_path)
        .map_err(|io_error| protocol(format!("{output_name}: {io_error}")))?;
    if !metadata.is_file() {
        return Err(protocol(format!("{output_name} is not a regular file")));
    }
    if metadata.len() > limits.max_child_output_bytes {
        return Err(Diagnostic::new(
            code!("LLS8002"),
            format!(
                "max_child_output_bytes exceeded by the pdf output: configured {}, produced {}",
                limits.max_child_output_bytes,
                metadata.len()
            ),
        ));
    }
    let pdf_bytes = std::fs::read(&output_path)
        .map_err(|io_error| protocol(format!("{output_name}: {io_error}")))?;
    if pdf_bytes.len() as u64 > limits.max_child_output_bytes {
        return Err(Diagnostic::new(
            code!("LLS8002"),
            format!(
                "max_child_output_bytes exceeded by the pdf output: configured {}, produced {}",
                limits.max_child_output_bytes,
                pdf_bytes.len()
            ),
        ));
    }
    if !pdf_bytes.starts_with(b"%PDF-") {
        return Err(protocol("the provider output does not begin with %PDF-"));
    }
    let pdf_sha256 = Sha256Digest::of(&pdf_bytes);

    // §19.8: the recipe content address over configured inputs.
    let argv_json = Json::Arr(
        provider
            .compile_argv
            .iter()
            .cloned()
            .map(Json::Str)
            .collect(),
    )
    .to_canonical_string();
    let resources_json = Json::Arr(
        resource_rows
            .iter()
            .map(|(path, sha256)| {
                Json::object(vec![
                    ("path", Json::Str(path.clone())),
                    ("sha256", Json::Str(sha256.to_hex())),
                ])
            })
            .collect(),
    )
    .to_canonical_string();
    let recipe_id = pdf_recipe_id(
        Sha256Digest::of(tex_bytes),
        provider.program_sha256,
        provider.version_stdout_sha256,
        &argv_json,
        &resources_json,
    );

    Ok(PdfResult {
        recipe_id,
        pdf_bytes,
        pdf_sha256,
        version,
        compile,
    })
}
