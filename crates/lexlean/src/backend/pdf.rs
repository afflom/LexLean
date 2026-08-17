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

use camino::{Utf8Path, Utf8PathBuf};

use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::{pdf_recipe_id, Sha256Digest};
use crate::code;
use crate::config::PdfProvider;
use crate::diagnostic::Diagnostic;
use crate::project::Project;
use crate::verify::child::{run as run_child, ChildHome, ChildRecord, ChildSpec, Normalizer};

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
    /// The version probe record (tool `pdf`, argv as configured, output
    /// normalized by the verification normalizer).
    pub version: ChildRecord,
    /// The compile record (argv after placeholder expansion).
    pub compile: ChildRecord,
}

fn protocol(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLB6004"), message)
}

fn policy(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLS8004"), message)
}

/// Run one provider process through the shared child runner (§25.2,
/// §25.4, §25.5): the isolated temporary home, no inherited proxy
/// variables, no shell, and the configured timeout and output caps with
/// checked arithmetic. A provider that cannot be started is a protocol
/// failure (LLB6004), not a toolchain mismatch.
fn run_provider_process(
    project: &Project,
    program: &Utf8Path,
    argv: &[String],
    workdir: &Utf8Path,
    home: &Utf8Path,
    stem: &str,
    executable_sha256: Sha256Digest,
    normalizer: &Normalizer,
) -> Result<ChildRecord, Diagnostic> {
    run_child(
        &ChildSpec {
            tool: "pdf",
            module: Some(stem.to_owned()),
            program,
            executable_sha256,
            argv: argv.to_vec(),
            cwd: workdir,
            extra_env: Vec::new(),
            home: ChildHome::Isolated { home },
        },
        &project.config.limits,
        normalizer,
    )
    .map_err(|diagnostic| {
        if diagnostic.code.as_str() == "LLV7001" {
            protocol(diagnostic.message)
        } else {
            diagnostic
        }
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
    normalizer: &Normalizer,
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
    let workspace_root = Utf8PathBuf::from_path_buf(workspace.path().to_path_buf())
        .map_err(|bad| crate::project::non_utf8_path(&bad))?;
    let workdir = workspace_root.join("work");
    let out_dir = workspace_root.join("out");
    let home = workspace_root.join("home");
    for directory in [&workdir, &out_dir, &home] {
        std::fs::create_dir_all(directory.as_std_path())
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
    std::fs::write(workdir.join(&tex_name).as_std_path(), tex_bytes)
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
        std::fs::write(workdir.join(name).as_std_path(), &bytes)
            .map_err(|io_error| protocol(format!("pdf staging: {io_error}")))?;
        resource_rows.push((resource.clone(), Sha256Digest::of(&bytes)));
    }
    resource_rows.sort_by(|a, b| a.0.cmp(&b.0));

    // 2–3. The version probe with no shell, stdout normalized and checked.
    let version = run_provider_process(
        project,
        &program_path,
        &provider.version_argv,
        &workdir,
        &home,
        stem,
        program_sha256,
        normalizer,
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
            "{out_dir}" => out_dir.to_string(),
            "{stem}" => stem.to_owned(),
            other => other.to_owned(),
        })
        .collect();
    let compile = run_provider_process(
        project,
        &program_path,
        &expanded,
        &workdir,
        &home,
        stem,
        program_sha256,
        normalizer,
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
    for entry in std::fs::read_dir(out_dir.as_std_path())
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
    let metadata = std::fs::symlink_metadata(output_path.as_std_path())
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
    let pdf_bytes = std::fs::read(output_path.as_std_path())
        .map_err(|io_error| protocol(format!("{output_name}: {io_error}")))?;
    if u64::try_from(pdf_bytes.len()).unwrap_or(u64::MAX) > limits.max_child_output_bytes {
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
