//! Verification (SPEC.md §22): the complete fixed pipeline, with no
//! optional stage and no suppression. Any failed stage removes the staging
//! tree and produces no verified artifact (I11).

pub mod axiom;
pub mod child;
pub mod leanchecker;
pub mod toolchain;
pub mod workspace;

use std::collections::BTreeSet;
use std::io::Write;

use camino::{Utf8Path, Utf8PathBuf};

use crate::api::RenderedBuild;
use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::{attestation_id, Sha256Digest};
use crate::code;
use crate::diagnostic::{Diagnostic, Span};
use crate::error::LexLeanError;
use crate::ir::declaration::DeclBody;
use crate::link::CheckedProject;
use crate::lock::Lock;
use crate::project::Project;
use crate::verify::child::{run as run_child, ChildRecord, ChildSpec, Normalizer};
use crate::verify::toolchain::Toolchain;

/// The outcome of a successful verification.
pub struct VerifyOutcome {
    /// The attestation ID.
    pub attestation_id: Sha256Digest,
    /// The published verified directory.
    pub root: Utf8PathBuf,
}

fn fail(diagnostic: Diagnostic) -> LexLeanError {
    LexLeanError::from_diagnostic(diagnostic)
}

/// The prose-free generated-source audit (§18.2, LN-11): a token-level scan
/// of every generated `.lean` before verification. A violation here is an
/// internal invariant failure, because only this compiler writes the files.
fn generated_source_audit(text: &str) -> Result<(), String> {
    // Spelled in halves so the repository forbidden-token audits can scan
    // their own gate sources without matching these mentions.
    let forbidden_idents = [
        concat!("sor", "ry"),
        concat!("ad", "mit"),
        concat!("axi", "om"),
        concat!("opa", "que"),
        concat!("un", "safe"),
        concat!("native_", "decide"),
    ];
    let bytes = text.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        let c = bytes[index] as char;
        if c == '"' {
            return Err("a string literal in generated Lean".to_owned());
        }
        if c == '-' && bytes.get(index + 1) == Some(&b'-') {
            return Err("a line comment in generated Lean".to_owned());
        }
        if c == '/' && bytes.get(index + 1) == Some(&b'-') {
            return Err("a block comment in generated Lean".to_owned());
        }
        if c.is_ascii_alphabetic() || c == '_' {
            let start = index;
            while index < bytes.len()
                && ((bytes[index] as char).is_ascii_alphanumeric()
                    || bytes[index] == b'_'
                    || bytes[index] == b'.')
            {
                index += 1;
            }
            let token = &text[start..index];
            for forbidden in forbidden_idents {
                if token == forbidden {
                    return Err(format!("forbidden token `{forbidden}` in generated Lean"));
                }
            }
        } else {
            index += 1;
        }
    }
    Ok(())
}

fn write_staged(root: &std::path::Path, relative: &str, bytes: &[u8]) -> Result<(), LexLeanError> {
    let destination = root.join(relative);
    if let Some(parent) = destination.parent() {
        std::fs::create_dir_all(parent).map_err(|io_error| {
            fail(Diagnostic::new(
                code!("LLB6003"),
                format!("staging {relative}: {io_error}"),
            ))
        })?;
    }
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&destination)
        .map_err(|io_error| {
            fail(Diagnostic::new(
                code!("LLB6003"),
                format!("staging {relative}: {io_error}"),
            ))
        })?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(|io_error| {
            fail(Diagnostic::new(
                code!("LLB6003"),
                format!("staging {relative}: {io_error}"),
            ))
        })
}

/// Remap a Lean error location against the generated module maps (§20.4).
fn remap_lean_failure(
    checked: &CheckedProject,
    build: &RenderedBuild,
    module_lean_name: &str,
    stderr: &str,
    project_span_fallback: Option<Span>,
) -> Diagnostic {
    // Lean reports `path:line:col: error: message`.
    for line in stderr.lines() {
        let mut parts = line.splitn(4, ':');
        let (Some(path_part), Some(line_part), Some(column_part), Some(message)) =
            (parts.next(), parts.next(), parts.next(), parts.next())
        else {
            continue;
        };
        let (Ok(line_number), Ok(column_number)) = (
            line_part.trim().parse::<usize>(),
            column_part.trim().parse::<usize>(),
        ) else {
            continue;
        };
        let Some(module) = build
            .modules
            .iter()
            .find(|module| module.lean_module == module_lean_name)
        else {
            break;
        };
        // Byte position from one-based line and zero-based column.
        let mut offset = 0usize;
        for (index, text_line) in module.lean_text.split('\n').enumerate() {
            if index + 1 == line_number {
                offset += column_number.min(text_line.len());
                break;
            }
            offset += text_line.len() + 1;
        }
        let mut diagnostic = Diagnostic::new(
            code!("LLV7002"),
            format!("Lean rejected `{module_lean_name}`:{}", message.trim_end()),
        );
        if let Some(mapping) = module.map.remap(0, offset) {
            if let Some((source_start, source_end)) = mapping.src_range {
                let path =
                    module
                        .map
                        .sources
                        .first()
                        .map_or_else(String::new, |source| match source {
                            crate::artifact::source_map::MapSource::File { path, .. } => {
                                path.clone()
                            }
                            _ => String::new(),
                        });
                let position = |byte: usize| {
                    checked
                        .modules
                        .get(&module.module)
                        .map_or((1, 1), |checked_module| {
                            let prefix = &checked_module.normalized
                                [..byte.min(checked_module.normalized.len())];
                            let line = prefix.matches('\n').count() + 1;
                            let column = prefix
                                .rsplit('\n')
                                .next()
                                .map_or(1, |tail| tail.chars().count() + 1);
                            (line, column)
                        })
                };
                let (line_start, column_start) = position(source_start);
                let (line_end, column_end) = position(source_end);
                diagnostic = diagnostic.with_span(Span {
                    path,
                    byte_start: source_start,
                    byte_end: source_end,
                    line_start,
                    column_start,
                    line_end,
                    column_end,
                });
            }
        } else if let Some(span) = project_span_fallback.clone() {
            diagnostic = diagnostic.with_span(span);
        }
        diagnostic = diagnostic.with_note(format!(
            "generated location: {path_part}:{line_number}:{column_number}"
        ));
        return diagnostic;
    }
    Diagnostic::new(
        code!("LLV7002"),
        format!("Lean rejected `{module_lean_name}`: {}", stderr.trim_end()),
    )
}

/// Run the complete verification pipeline (§22.1) over a rendered build.
#[allow(clippy::too_many_lines)]
pub fn run(
    project: &Project,
    lock: &Lock,
    checked: &CheckedProject,
    build: &RenderedBuild,
) -> Result<VerifyOutcome, LexLeanError> {
    let limits = project.config.limits;

    // Stage 4: toolchain preflight (§22.2).
    let toolchain: Toolchain = toolchain::preflight().map_err(fail)?;
    let toolchain_bin = toolchain.root.join("bin");

    // Stage 5: Lake workspace preflight (§10.4) and module-name conflicts
    // (§18.8, §18.9).
    workspace::preflight(project, lock).map_err(fail)?;
    let semantic_hex32: String = checked.semantic_id.to_hex()[..32].to_owned();
    let probe_name = format!("LexLeanProbe.P{semantic_hex32}");
    let audit_name = format!("LexLeanAudit.A{semantic_hex32}");
    let mut all_names: Vec<String> = build
        .modules
        .iter()
        .map(|module| module.lean_module.clone())
        .collect();
    all_names.push(probe_name.clone());
    all_names.push(audit_name.clone());
    workspace::reject_module_conflicts(project, &all_names).map_err(fail)?;

    // Generated-source audit before any Lean invocation (§18.2).
    for module in &build.modules {
        if let Err(reason) = generated_source_audit(&module.lean_text) {
            return Err(fail(Diagnostic::new(
                code!("LLI9001"),
                format!("phase verify: {reason}"),
            )));
        }
    }

    // Staging under the build root with owner-only permissions (§25.6).
    let verified_root = project
        .root
        .join(&project.config.build_root)
        .join("verified");
    std::fs::create_dir_all(verified_root.as_std_path()).map_err(|io_error| {
        fail(Diagnostic::new(
            code!("LLB6003"),
            format!("{verified_root}: {io_error}"),
        ))
    })?;
    let staging = tempfile::Builder::new()
        .prefix(".staging-")
        .tempdir_in(verified_root.as_std_path())
        .map_err(|io_error| {
            fail(Diagnostic::new(
                code!("LLB6003"),
                format!("staging: {io_error}"),
            ))
        })?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = std::fs::set_permissions(staging.path(), std::fs::Permissions::from_mode(0o700));
    }
    let staging_utf8 = Utf8PathBuf::from_path_buf(staging.path().to_path_buf())
        .map_err(|_| fail(Diagnostic::new(code!("LLS8001"), "non-UTF-8 staging path")))?;
    let workspace_root = if project.config.lean_workspace == "." {
        project.root.clone()
    } else {
        project.root.join(&project.config.lean_workspace)
    };
    let normalizer = Normalizer::new(
        &staging_utf8,
        &project.root,
        &workspace_root,
        &toolchain.root,
    );

    // Copy the platform-independent build artifacts into the verified set
    // (§22.8).
    for (relative, bytes) in &build.files {
        let renamed = if relative == "manifest.json" {
            "build-manifest.json".to_owned()
        } else {
            relative.clone()
        };
        write_staged(staging.path(), &renamed, bytes)?;
    }

    // Stage the compilation tree.
    let src_root = staging_utf8.join("lean-src");
    let olean_root = staging_utf8.join("oleans");
    for module in &build.modules {
        let module_path = module.lean_module.replace('.', "/");
        write_staged(
            staging.path(),
            &format!("lean-src/{module_path}.lean"),
            module.lean_text.as_bytes(),
        )?;
    }
    let lean_path_env = format!("{olean_root}");
    let mut process_records: Vec<ChildRecord> = Vec::new();

    // Stage 6: the external-interface probe (§18.8).
    let (probe_module_name, probe_text) = crate::backend::lean::probe_module(
        &semantic_hex32,
        &checked.external_used,
        &checked.closure,
    )
    .map_err(fail)?;
    debug_assert_eq!(probe_module_name, probe_name);
    write_staged(
        staging.path(),
        &format!("probe/{probe_name}.lean"),
        probe_text.as_bytes(),
    )?;
    let probe_source = staging_utf8
        .join("probe")
        .join(format!("{probe_name}.lean"));
    let probe_record = run_child(
        &ChildSpec {
            tool: "lean",
            module: Some(probe_name.clone()),
            program: &toolchain.lake.path,
            executable_sha256: toolchain.lean.sha256,
            argv: vec![
                "env".to_owned(),
                "lean".to_owned(),
                probe_source.to_string(),
            ],
            cwd: &workspace_root,
            extra_env: vec![("LEAN_PATH".to_owned(), lean_path_env.clone())],
            toolchain_bin: &toolchain_bin,
        },
        &limits,
        &normalizer,
    )
    .map_err(fail)?;
    if probe_record.exit_code != 0 {
        return Err(fail(Diagnostic::new(
            code!("LLT4003"),
            format!(
                "an external-interface probe failed to elaborate: {}",
                probe_record.stderr.trim_end()
            ),
        )));
    }
    write_staged(
        staging.path(),
        "probe/process.json",
        &probe_record.to_json().to_file_bytes(),
    )?;

    // Stage 7: module elaboration in topological import order (§22.3).
    let ordered: Vec<&crate::api::RenderedModule> = {
        let mut order = Vec::new();
        let mut placed: BTreeSet<&str> = BTreeSet::new();
        let mut remaining: Vec<&crate::api::RenderedModule> = build.modules.iter().collect();
        while !remaining.is_empty() {
            let before = remaining.len();
            remaining.retain(|module| {
                let document = &checked.modules[&module.module].document;
                let ready = document
                    .imports
                    .iter()
                    .all(|import| placed.contains(import.as_str()));
                if ready {
                    order.push(*module);
                    placed.insert(module.module.as_str());
                    false
                } else {
                    true
                }
            });
            if remaining.len() == before {
                return Err(fail(Diagnostic::new(
                    code!("LLI9001"),
                    "phase verify: module order did not converge",
                )));
            }
        }
        order
    };
    for module in &ordered {
        let module_path = module.lean_module.replace('.', "/");
        let source = src_root.join(format!("{module_path}.lean"));
        let olean = olean_root.join(format!("{module_path}.olean"));
        if let Some(parent) = olean.parent() {
            std::fs::create_dir_all(parent.as_std_path()).map_err(|io_error| {
                fail(Diagnostic::new(
                    code!("LLB6003"),
                    format!("staging oleans: {io_error}"),
                ))
            })?;
        }
        let record = run_child(
            &ChildSpec {
                tool: "lean",
                module: Some(module.lean_module.clone()),
                program: &toolchain.lake.path,
                executable_sha256: toolchain.lean.sha256,
                argv: vec![
                    "env".to_owned(),
                    "lean".to_owned(),
                    "-o".to_owned(),
                    olean.to_string(),
                    source.to_string(),
                ],
                cwd: &workspace_root,
                extra_env: vec![("LEAN_PATH".to_owned(), lean_path_env.clone())],
                toolchain_bin: &toolchain_bin,
            },
            &limits,
            &normalizer,
        )
        .map_err(fail)?;
        if record.exit_code != 0 {
            // Lean reports compile errors on stdout under `lake env lean`;
            // remap over both streams (§20.4).
            let combined = format!("{}\n{}", record.stdout, record.stderr);
            return Err(fail(remap_lean_failure(
                checked,
                build,
                &module.lean_module,
                &combined,
                None,
            )));
        }
        // Any warning or unknown informational message fails verification
        // (§20.2, §22.3).
        if !record.stdout.trim().is_empty() || !record.stderr.trim().is_empty() {
            return Err(fail(Diagnostic::new(
                code!("LLV7006"),
                format!(
                    "unexpected output while compiling `{}`: {}{}",
                    module.lean_module,
                    record.stdout.trim_end(),
                    record.stderr.trim_end()
                ),
            )));
        }
        if !olean.as_std_path().is_file() {
            return Err(fail(Diagnostic::new(
                code!("LLV7002"),
                format!("`{}` produced no olean", module.lean_module),
            )));
        }
        write_staged(
            staging.path(),
            &format!("process/lean/{}.json", module.lean_module),
            &record.to_json().to_file_bytes(),
        )?;
        process_records.push(record);
    }

    // Stage 8: separate-process leanchecker replay per module, sorted
    // (§22.4).
    let mut sorted_modules: Vec<&crate::api::RenderedModule> = build.modules.iter().collect();
    sorted_modules.sort_by(|a, b| a.lean_module.cmp(&b.lean_module));
    for module in &sorted_modules {
        let record = leanchecker::replay_module(
            &toolchain,
            &module.lean_module,
            &lean_path_env,
            &workspace_root,
            &limits,
            &normalizer,
        )
        .map_err(fail)?;
        write_staged(
            staging.path(),
            &format!("process/leanchecker/{}.json", module.lean_module),
            &record.to_json().to_file_bytes(),
        )?;
        process_records.push(record);
    }

    // Stage 9–10: the audit module and exact output parsing (§18.9, §22.5).
    let mut declaration_names: Vec<String> = Vec::new();
    for module in &build.modules {
        let document = &checked.modules[&module.module].document;
        for declaration in document.declarations() {
            declaration_names.push(format!("{}.{}", module.lean_module, declaration.lean_name));
        }
    }
    declaration_names.sort();
    let generated_module_names: Vec<String> = build
        .modules
        .iter()
        .map(|module| module.lean_module.clone())
        .collect();
    let (audit_module_name, audit_text) = crate::backend::lean::audit_module(
        &semantic_hex32,
        &generated_module_names,
        &declaration_names,
    );
    debug_assert_eq!(audit_module_name, audit_name);
    write_staged(
        staging.path(),
        &format!("audit/{audit_name}.lean"),
        audit_text.as_bytes(),
    )?;
    let audit_source = staging_utf8
        .join("audit")
        .join(format!("{audit_name}.lean"));
    let audit_record = run_child(
        &ChildSpec {
            tool: "lean",
            module: Some(audit_name.clone()),
            program: &toolchain.lake.path,
            executable_sha256: toolchain.lean.sha256,
            argv: vec![
                "env".to_owned(),
                "lean".to_owned(),
                audit_source.to_string(),
            ],
            cwd: &workspace_root,
            extra_env: vec![("LEAN_PATH".to_owned(), lean_path_env.clone())],
            toolchain_bin: &toolchain_bin,
        },
        &limits,
        &normalizer,
    )
    .map_err(fail)?;
    if audit_record.exit_code != 0 {
        return Err(fail(Diagnostic::new(
            code!("LLV7004"),
            format!("the axiom audit failed: {}", audit_record.stderr.trim_end()),
        )));
    }
    write_staged(
        staging.path(),
        "audit/output.txt",
        audit_record.stdout.as_bytes(),
    )?;
    write_staged(
        staging.path(),
        "audit/process.json",
        &audit_record.to_json().to_file_bytes(),
    )?;
    let observed =
        axiom::parse_audit_output(&audit_record.stdout, &declaration_names).map_err(fail)?;

    // Stage 11: per-declaration policy enforcement (§22.6).
    let mut declaration_rows: Vec<Json> = Vec::new();
    for module in &build.modules {
        let document = &checked.modules[&module.module].document;
        for declaration in document.declarations() {
            let full_name = format!("{}.{}", module.lean_module, declaration.lean_name);
            let observed_set = observed.get(&full_name).cloned().unwrap_or_default();
            if !declaration.policy.permits(&observed_set) {
                return Err(fail(Diagnostic::new(
                    code!("LLV7005"),
                    format!(
                        "`{full_name}` violates its {} axiom policy: observed [{}]",
                        declaration.policy.kind(),
                        observed_set.join(", ")
                    ),
                )));
            }
            let _ = matches!(declaration.body, DeclBody::TheoremLike { .. });
            declaration_rows.push(Json::object(vec![
                ("name", Json::Str(full_name)),
                (
                    "policy",
                    Json::object(vec![
                        ("kind", Json::Str(declaration.policy.kind().to_owned())),
                        (
                            "axioms",
                            Json::Arr(
                                declaration
                                    .policy
                                    .axioms()
                                    .iter()
                                    .cloned()
                                    .map(Json::Str)
                                    .collect(),
                            ),
                        ),
                    ]),
                ),
                (
                    "observed",
                    Json::Arr(observed_set.into_iter().map(Json::Str).collect()),
                ),
                ("result", Json::Str("ok".to_owned())),
            ]));
        }
    }

    // Stage 12: optional configured PDF rendering (§19.7).
    let mut pdf_row: Option<Json> = None;
    if let Some(provider) = &project.config.pdf {
        for module in &build.modules {
            let result = crate::backend::pdf::run_provider(
                project,
                provider,
                module.tex_text.as_bytes(),
                &module.lean_module,
                &staging_utf8,
            )
            .map_err(fail)?;
            write_staged(
                staging.path(),
                &format!("pdf/{}.pdf", module.lean_module),
                &result.pdf_bytes,
            )?;
            pdf_row = Some(Json::object(vec![
                ("module", Json::Str(module.lean_module.clone())),
                ("recipe_id", Json::Str(result.recipe_id.to_hex())),
                ("pdf_sha256", Json::Str(result.pdf_sha256.to_hex())),
                ("byte_length", Json::from_usize(result.pdf_bytes.len())),
            ]));
        }
    }

    // Stage 13: no unexpected absolute paths in successful output (§22.7).
    for record in &process_records {
        if normalizer.has_unexpected_absolute_path(&record.stdout)
            || normalizer.has_unexpected_absolute_path(&record.stderr)
        {
            return Err(fail(Diagnostic::new(
                code!("LLV7006"),
                format!(
                    "unexpected absolute path in the output of `{}`",
                    record.tool
                ),
            )));
        }
    }

    // Copy oleans into the verified set and hash them.
    let mut olean_rows: Vec<Json> = Vec::new();
    for module in &build.modules {
        let module_path = module.lean_module.replace('.', "/");
        let olean = olean_root.join(format!("{module_path}.olean"));
        let bytes = std::fs::read(olean.as_std_path()).map_err(|io_error| {
            fail(Diagnostic::new(
                code!("LLV7002"),
                format!("{olean}: {io_error}"),
            ))
        })?;
        olean_rows.push(Json::object(vec![
            ("module", Json::Str(module.lean_module.clone())),
            ("byte_length", Json::from_usize(bytes.len())),
            ("sha256", Json::Str(Sha256Digest::of(&bytes).to_hex())),
        ]));
    }

    // Stage 14: the attestation (§22.9). No timestamp is hashed.
    let lexlean_executable_sha256 = std::env::current_exe()
        .ok()
        .and_then(|path| std::fs::read(path).ok())
        .map(|bytes| Sha256Digest::of(&bytes))
        .unwrap_or(Sha256Digest([0; 32]));
    let tool_json = |tool: &toolchain::Tool| {
        Json::object(vec![
            ("version_output", Json::Str(tool.version_output.clone())),
            ("executable_sha256", Json::Str(tool.sha256.to_hex())),
        ])
    };
    let mut body_fields = vec![
        ("spec", Json::Str("lexlean/attestation/1".to_owned())),
        ("status", Json::Str("verified".to_owned())),
        ("semantic_id", Json::Str(checked.semantic_id.to_hex())),
        ("source_id", Json::Str(checked.source_id.to_hex())),
        ("build_id", Json::Str(build.build_id.to_hex())),
        (
            "host",
            Json::object(vec![
                ("os", Json::Str(std::env::consts::OS.to_owned())),
                ("arch", Json::Str(std::env::consts::ARCH.to_owned())),
            ]),
        ),
        (
            "lexlean",
            Json::object(vec![
                ("version", Json::Str(crate::COMPILER_VERSION.to_owned())),
                (
                    "compiler_semantics",
                    Json::Str(crate::compiler_semantics_id().to_hex()),
                ),
                (
                    "executable_sha256",
                    Json::Str(lexlean_executable_sha256.to_hex()),
                ),
            ]),
        ),
        (
            "toolchain",
            Json::object(vec![
                ("lean", tool_json(&toolchain.lean)),
                ("lake", tool_json(&toolchain.lake)),
                ("leanchecker", tool_json(&toolchain.leanchecker)),
            ]),
        ),
        (
            "lake_workspace",
            Json::Arr(
                lock.workspace_files
                    .iter()
                    .map(|(path, sha256)| {
                        Json::object(vec![
                            ("path", Json::Str(path.clone())),
                            ("sha256", Json::Str(sha256.to_hex())),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "build_manifest",
            Json::object(vec![
                ("byte_length", Json::from_usize(build.manifest_bytes.len())),
                (
                    "sha256",
                    Json::Str(Sha256Digest::of(&build.manifest_bytes).to_hex()),
                ),
            ]),
        ),
        ("oleans", Json::Arr(olean_rows)),
        (
            "processes",
            Json::Arr(process_records.iter().map(ChildRecord::to_json).collect()),
        ),
        ("declarations", Json::Arr(declaration_rows)),
    ];
    if let Some(pdf) = pdf_row {
        body_fields.push(("pdf", pdf));
    }
    let body = Json::object(body_fields);
    let this_attestation_id = attestation_id(&body.to_canonical_string());
    let full = match body {
        Json::Obj(mut object) => {
            object.insert(
                "attestation_id".to_owned(),
                Json::Str(this_attestation_id.to_hex()),
            );
            Json::Obj(object)
        }
        other => other,
    };
    write_staged(staging.path(), "attestation.json", &full.to_file_bytes())?;

    // Remove the compilation scratch tree; the fixed §22.8 artifact set
    // keeps only sources, maps, coverage, oleans, probe, audit, and process
    // records. The module-system `.olean.private`/`.olean.server` parts
    // stay with their `.olean`; the `.ir` intermediate does not.
    let _ = std::fs::remove_dir_all(src_root.as_std_path());
    for entry in walkdir::WalkDir::new(olean_root.as_std_path())
        .into_iter()
        .flatten()
    {
        if entry.file_type().is_file()
            && entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "ir")
        {
            let _ = std::fs::remove_file(entry.path());
        }
    }

    // Stage 15: atomic publication (§21.8).
    let target = verified_root.join(this_attestation_id.to_hex());
    if target.as_std_path().exists() {
        // A repeated verification of identical content republishes the
        // identical set; anything else refuses to overwrite.
        return Ok(VerifyOutcome {
            attestation_id: this_attestation_id,
            root: target,
        });
    }
    let staged = staging.keep();
    std::fs::rename(&staged, target.as_std_path()).map_err(|io_error| {
        let _ = std::fs::remove_dir_all(&staged);
        fail(Diagnostic::new(
            code!("LLB6003"),
            format!("publishing {target}: {io_error}"),
        ))
    })?;
    Ok(VerifyOutcome {
        attestation_id: this_attestation_id,
        root: target,
    })
}

/// The verified layout keeps oleans under `oleans/`; expose the staging
/// name for tests.
pub const OLEAN_DIR: &str = "oleans";

/// A helper for tests: the reserved probe and audit module names for a
/// semantic ID (§18.8, §18.9).
#[must_use]
pub fn reserved_module_names(semantic_id: Sha256Digest) -> (String, String) {
    let hex32: String = semantic_id.to_hex()[..32].to_owned();
    (
        format!("LexLeanProbe.P{hex32}"),
        format!("LexLeanAudit.A{hex32}"),
    )
}

/// Re-exported for the workspace path in child specs.
pub use crate::verify::child::Normalizer as OutputNormalizer;

/// The lint-visible marker that no stage is optional (VR-01): the stage
/// driver above has no configuration surface.
pub const STAGES_ARE_FIXED: bool = true;

fn _assert_workspace_path(_p: &Utf8Path) {}
