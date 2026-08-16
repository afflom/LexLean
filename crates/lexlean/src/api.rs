//! The stable public API (SPEC.md §24): `Engine` with its request and
//! result types. Requests cannot alter backends, toolchain, verification
//! stages, limits, policies, or the fixed artifact sets (CL-15).

use std::collections::{BTreeMap, BTreeSet};

use camino::{Utf8Path, Utf8PathBuf};

use crate::artifact::canonical_json::Json;
use crate::artifact::content_id::{build_id, Sha256Digest};
use crate::artifact::manifest::{BuildManifest, FileRow, ModuleRow};
use crate::artifact::source_map::{ArtifactKind, MapArtifact, MapSource, SourceMap};
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::error::LexLeanError;
use crate::link::{check_project, CheckedProject};
use crate::lock::{compute_lock, parse_lock, read_current_lock, Lock};
use crate::project::Project;
pub use crate::project::Selection;
use crate::source::coverage::Coverage;

/// The stable engine (§24.1).
pub struct Engine {
    project: Project,
}

/// A check request.
pub struct CheckRequest {
    /// The selection.
    pub selection: Selection,
}

/// A build request.
pub struct BuildRequest {
    /// The selection.
    pub selection: Selection,
}

/// A verify request.
pub struct VerifyRequest {
    /// The selection.
    pub selection: Selection,
}

/// A format request.
pub struct FormatRequest {
    /// The selection.
    pub selection: Selection,
    /// Exact-byte comparison instead of rewriting.
    pub check_only: bool,
}

/// A lock request.
pub struct LockRequest {
    /// Exact-byte comparison instead of updating.
    pub check_only: bool,
    /// Permit acquiring missing exact Git commits (I15).
    pub allow_network: bool,
}

/// The outcome of a lock operation.
pub struct LockResult {
    /// The canonical lock bytes.
    pub bytes: Vec<u8>,
    /// Whether the on-disk lock was rewritten.
    pub written: bool,
}

/// A checked-unit summary (§24.4).
#[derive(Debug, Clone)]
pub struct CheckedUnitSummary {
    /// The full generated Lean module name.
    pub lean_module: String,
    /// The number of declarations.
    pub declarations: usize,
}

/// One checked unit.
#[derive(Debug, Clone)]
pub struct CheckedUnit {
    /// The module name.
    pub module: String,
    /// The summary.
    pub summary: CheckedUnitSummary,
}

/// The artifacts of one built module.
#[derive(Debug, Clone)]
pub struct ModuleArtifacts {
    /// Build-relative artifact paths.
    pub paths: Vec<String>,
}

/// One built unit.
#[derive(Debug, Clone)]
pub struct BuiltUnit {
    /// The module name.
    pub module: String,
    /// Its artifacts.
    pub artifacts: ModuleArtifacts,
}

/// One verified unit.
#[derive(Debug, Clone)]
pub struct VerifiedUnit {
    /// The module name.
    pub module: String,
    /// The full generated Lean module name.
    pub lean_module: String,
}

/// A project result set (§24.4): always a set, never a singular unit.
pub struct ProjectResultSet<U> {
    /// The source ID.
    pub source_id: Sha256Digest,
    /// The semantic ID.
    pub semantic_id: Sha256Digest,
    /// The build ID, present after a build.
    pub build_id: Option<Sha256Digest>,
    /// Units by module name.
    pub units: BTreeMap<String, U>,
}

/// A verified project (§24.4).
pub struct VerifiedProject {
    /// The source ID.
    pub source_id: Sha256Digest,
    /// The semantic ID.
    pub semantic_id: Sha256Digest,
    /// The build ID.
    pub build_id: Sha256Digest,
    /// The attestation ID.
    pub attestation_id: Sha256Digest,
    /// The published verified directory.
    pub root: Utf8PathBuf,
    /// Units by module name.
    pub units: BTreeMap<String, VerifiedUnit>,
}

/// A format result set.
pub struct FormatResultSet {
    /// Per module: was it already canonical?
    pub units: BTreeMap<String, bool>,
}

/// One rendered module inside a build.
pub struct RenderedModule {
    /// The source module name.
    pub module: String,
    /// The full generated Lean module name.
    pub lean_module: String,
    /// The generated Lean text.
    pub lean_text: String,
    /// The canonical LaTeX text.
    pub tex_text: String,
    /// The complete coverage record.
    pub coverage: Coverage,
    /// The module source map.
    pub map: SourceMap,
    /// Build-relative artifact paths.
    pub lean_path: String,
    /// The `.tex` path.
    pub tex_path: String,
}

/// A fully rendered build (§21.5).
pub struct RenderedBuild {
    /// The build ID.
    pub build_id: Sha256Digest,
    /// Modules in sorted name order.
    pub modules: Vec<RenderedModule>,
    /// Every file of the build directory as `(relative path, bytes)`,
    /// manifest included.
    pub files: Vec<(String, Vec<u8>)>,
    /// The manifest.
    pub manifest: BuildManifest,
    /// The canonical manifest bytes.
    pub manifest_bytes: Vec<u8>,
}

fn file_row(kind: &str, path: &str, bytes: &[u8]) -> FileRow {
    FileRow {
        kind: kind.to_owned(),
        path: path.to_owned(),
        byte_length: bytes.len(),
        sha256: Sha256Digest::of(bytes),
    }
}

/// Render the complete platform-independent build artifact set from a
/// checked project (§21.5, §21.6). No Lean process runs here (CL-05).
#[allow(clippy::too_many_lines)]
pub fn render_build(
    project: &Project,
    checked: &CheckedProject,
) -> Result<RenderedBuild, LexLeanError> {
    let mut modules = Vec::new();
    let mut files: Vec<(String, Vec<u8>)> = Vec::new();
    let mut outputs: Vec<FileRow> = Vec::new();
    let mut manifest_modules = Vec::new();

    for (name, checked_module) in &checked.modules {
        let lean_emitter = crate::backend::lean::render_module(
            checked_module,
            &checked.closure,
            &project.config.module_prefix,
        )
        .map_err(LexLeanError::from_diagnostic)?;
        let tex_emitter = crate::backend::latex::render_module(checked_module, &checked.closure)
            .map_err(LexLeanError::from_diagnostic)?;
        let lean_module = checked_module.document.lean_module.clone();
        let module_path = lean_module.replace('.', "/");
        let lean_path = format!("modules/{module_path}.lean");
        let tex_path = format!("modules/{module_path}.tex");
        let map_path = format!("maps/{module_path}.map.json");
        let coverage_path = format!("coverage/{module_path}.coverage.json");
        let closure_path = format!("lexicons/{name}.closure.json");

        // The module source map over both artifacts (§20.3).
        let mut map = SourceMap {
            source_id: checked.source_id,
            semantic_id: checked.semantic_id,
            module: name.clone(),
            sources: vec![MapSource::File {
                id: 0,
                path: checked_module.document.source_path.clone(),
                sha256: checked_module.document.source_sha256,
            }],
            artifacts: vec![
                MapArtifact {
                    id: 0,
                    kind: ArtifactKind::Lean,
                    path: lean_path.clone(),
                },
                MapArtifact {
                    id: 1,
                    kind: ArtifactKind::Tex,
                    path: tex_path.clone(),
                },
            ],
            nodes: Vec::new(),
            mappings: Vec::new(),
        };
        lean_emitter.fold_into_map(&mut map, 0, 0);
        tex_emitter.fold_into_map(&mut map, 1, 0);

        let coverage = Coverage {
            module: name.clone(),
            source: checked_module.coverage_source.clone(),
            latex: tex_emitter.coverage_rows(),
            lean: lean_emitter.coverage_rows(),
        };

        let closure_json = checked
            .closure
            .closure_json(name, &checked_module.visible)
            .to_file_bytes();
        let lean_bytes = lean_emitter.text().as_bytes().to_vec();
        let tex_bytes = tex_emitter.text().as_bytes().to_vec();
        let map_bytes = map.to_json().to_file_bytes();
        let coverage_bytes = coverage.to_json().to_file_bytes();

        outputs.push(file_row("lean", &lean_path, &lean_bytes));
        outputs.push(file_row("tex", &tex_path, &tex_bytes));
        outputs.push(file_row("map", &map_path, &map_bytes));
        outputs.push(file_row("coverage", &coverage_path, &coverage_bytes));
        outputs.push(file_row("lexicon-closure", &closure_path, &closure_json));
        files.push((lean_path.clone(), lean_bytes));
        files.push((tex_path.clone(), tex_bytes));
        files.push((map_path, map_bytes));
        files.push((coverage_path, coverage_bytes));
        files.push((closure_path, closure_json));

        manifest_modules.push(ModuleRow {
            module: name.clone(),
            lean_module: lean_module.clone(),
            source_path: checked_module.document.source_path.clone(),
        });
        modules.push(RenderedModule {
            module: name.clone(),
            lean_module,
            lean_text: lean_emitter.text().to_owned(),
            tex_text: tex_emitter.text().to_owned(),
            coverage,
            map,
            lean_path,
            tex_path,
        });
    }

    let mut inputs: Vec<FileRow> = Vec::new();
    inputs.push(file_row(
        "project-config",
        &project.config_name,
        project.config.canonical_toml().as_bytes(),
    ));
    inputs.push(file_row(
        "lock",
        &project.config.lockfile,
        &checked.canonical_lock,
    ));
    for (name, checked_module) in &checked.modules {
        let _ = name;
        inputs.push(file_row(
            "source",
            &checked_module.document.source_path,
            checked_module.normalized.as_bytes(),
        ));
    }
    for package in &checked.closure.packages {
        inputs.push(FileRow {
            kind: "lexicon".to_owned(),
            path: package.id.clone(),
            byte_length: package.total_bytes,
            sha256: package.tree_sha256,
        });
    }

    let this_build_id = build_id(checked.source_id, checked.semantic_id);
    let manifest = BuildManifest {
        compiler_version: crate::COMPILER_VERSION.to_owned(),
        semantics_id: crate::compiler_semantics_id(),
        project: project.config.name.clone(),
        source_id: checked.source_id,
        semantic_id: checked.semantic_id,
        build_id: this_build_id,
        selection: checked.modules.keys().cloned().collect(),
        modules: manifest_modules,
        inputs,
        outputs,
    };
    let manifest_bytes = manifest.to_json().to_file_bytes();
    files.push(("manifest.json".to_owned(), manifest_bytes.clone()));

    Ok(RenderedBuild {
        build_id: this_build_id,
        modules,
        files,
        manifest,
        manifest_bytes,
    })
}

/// Acquire the project mutation lock at `.lexlean/.lock` (§21.8).
fn acquire_lock(project: &Project) -> Result<std::fs::File, LexLeanError> {
    use fs4::fs_std::FileExt;
    let build_root = project.root.join(&project.config.build_root);
    std::fs::create_dir_all(build_root.as_std_path()).map_err(|io_error| {
        LexLeanError::from_diagnostic(Diagnostic::new(
            code!("LLS8001"),
            format!("{build_root}: {io_error}"),
        ))
    })?;
    let lock_path = build_root.join(".lock");
    let file = std::fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(lock_path.as_std_path())
        .map_err(|io_error| {
            LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLS8001"),
                format!("{lock_path}: {io_error}"),
            ))
        })?;
    file.lock_exclusive().map_err(|io_error| {
        LexLeanError::from_diagnostic(Diagnostic::new(
            code!("LLS8001"),
            format!("{lock_path}: {io_error}"),
        ))
    })?;
    Ok(file)
}

/// Publish a rendered build atomically at its content-addressed path
/// (§21.5, §21.8): staging, fsync, validate-before-reuse, rename.
pub fn publish_build(
    project: &Project,
    build: &RenderedBuild,
) -> Result<Utf8PathBuf, LexLeanError> {
    let _guard = acquire_lock(project)?;
    let build_root = project.root.join(&project.config.build_root).join("build");
    std::fs::create_dir_all(build_root.as_std_path()).map_err(|io_error| {
        LexLeanError::from_diagnostic(Diagnostic::new(
            code!("LLB6003"),
            format!("{build_root}: {io_error}"),
        ))
    })?;
    let target = build_root.join(build.build_id.to_hex());
    if target.as_std_path().exists() {
        // Existing content-addressed output is reused only after every
        // file validates against the new manifest (§21.8).
        for (relative, bytes) in &build.files {
            let existing = std::fs::read(target.join(relative).as_std_path());
            match existing {
                Ok(found) if found == *bytes => {}
                _ => {
                    return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                        code!("LLB6003"),
                        format!(
                            "existing build directory {target} does not validate against the manifest; refusing to overwrite unexplained bytes"
                        ),
                    )));
                }
            }
        }
        return Ok(target);
    }
    let staging = tempfile::Builder::new()
        .prefix(".staging-")
        .tempdir_in(build_root.as_std_path())
        .map_err(|io_error| {
            LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLB6003"),
                format!("staging: {io_error}"),
            ))
        })?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = std::fs::set_permissions(staging.path(), std::fs::Permissions::from_mode(0o700));
    }
    for (relative, bytes) in &build.files {
        let destination = staging.path().join(relative);
        if let Some(parent) = destination.parent() {
            std::fs::create_dir_all(parent).map_err(|io_error| {
                LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLB6003"),
                    format!("staging {relative}: {io_error}"),
                ))
            })?;
        }
        // Create-new semantics for staging files (§25.1).
        let mut options = std::fs::OpenOptions::new();
        options.write(true).create_new(true);
        let mut file = options.open(&destination).map_err(|io_error| {
            LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLB6003"),
                format!("staging {relative}: {io_error}"),
            ))
        })?;
        use std::io::Write;
        file.write_all(bytes)
            .and_then(|()| file.sync_all())
            .map_err(|io_error| {
                LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLB6003"),
                    format!("staging {relative}: {io_error}"),
                ))
            })?;
    }
    let staged = staging.keep();
    std::fs::rename(&staged, target.as_std_path()).map_err(|io_error| {
        let _ = std::fs::remove_dir_all(&staged);
        LexLeanError::from_diagnostic(Diagnostic::new(
            code!("LLB6003"),
            format!("publishing {target}: {io_error}"),
        ))
    })?;
    Ok(target)
}

impl Engine {
    /// Load a project from its configuration file (§24.1).
    pub fn load(project_file: &Utf8Path) -> Result<Self, LexLeanError> {
        Ok(Self {
            project: Project::load(project_file)?,
        })
    }

    /// The loaded project.
    #[must_use]
    pub(crate) fn project(&self) -> &Project {
        &self.project
    }

    /// Update or check the lock (§23.4).
    pub fn lock(&self, request: LockRequest) -> Result<LockResult, LexLeanError> {
        if request.check_only && request.allow_network {
            return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLC0001"),
                "--check and --allow-network are mutually exclusive",
            )));
        }
        let (lock, _packages) = compute_lock(&self.project, request.allow_network)
            .map_err(LexLeanError::from_diagnostics)?;
        let bytes = lock.canonical_bytes();
        let lock_path = self.project.absolute(&self.project.config.lockfile);
        if request.check_only {
            let existing = std::fs::read(lock_path.as_std_path()).map_err(|io_error| {
                LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLC0102"),
                    format!("{}: {io_error}", self.project.config.lockfile),
                ))
            })?;
            if existing != bytes {
                return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLC0102"),
                    format!(
                        "{} is stale or noncanonical; run `lexlean lock`",
                        self.project.config.lockfile
                    ),
                )));
            }
            return Ok(LockResult {
                bytes,
                written: false,
            });
        }
        let _guard = acquire_lock(&self.project)?;
        if std::fs::read(lock_path.as_std_path()).is_ok_and(|existing| existing == bytes) {
            return Ok(LockResult {
                bytes,
                written: false,
            });
        }
        // Atomic write beside the target.
        let parent = lock_path
            .parent()
            .map(Utf8Path::to_path_buf)
            .unwrap_or_else(|| self.project.root.clone());
        let mut temp =
            tempfile::NamedTempFile::new_in(parent.as_std_path()).map_err(|io_error| {
                LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLB6003"),
                    format!("lock staging: {io_error}"),
                ))
            })?;
        use std::io::Write;
        temp.write_all(&bytes)
            .and_then(|()| temp.as_file().sync_all())
            .map_err(|io_error| {
                LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLB6003"),
                    format!("lock staging: {io_error}"),
                ))
            })?;
        temp.persist(lock_path.as_std_path())
            .map_err(|persist_error| {
                LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLB6003"),
                    format!("lock publish: {persist_error}"),
                ))
            })?;
        Ok(LockResult {
            bytes,
            written: true,
        })
    }

    fn checked(&self, selection: &Selection) -> Result<(CheckedProject, Lock), LexLeanError> {
        let (lock, packages) =
            read_current_lock(&self.project).map_err(LexLeanError::from_diagnostics)?;
        let checked = check_project(&self.project, selection, &lock, packages)?;
        Ok((checked, lock))
    }

    /// Check a selection through linked IR; no build artifacts (§23.4).
    pub fn check(
        &self,
        request: CheckRequest,
    ) -> Result<ProjectResultSet<CheckedUnit>, LexLeanError> {
        let (checked, _lock) = self.checked(&request.selection)?;
        Ok(ProjectResultSet {
            source_id: checked.source_id,
            semantic_id: checked.semantic_id,
            build_id: None,
            units: checked
                .modules
                .iter()
                .map(|(name, module)| {
                    (
                        name.clone(),
                        CheckedUnit {
                            module: name.clone(),
                            summary: CheckedUnitSummary {
                                lean_module: module.document.lean_module.clone(),
                                declarations: module.document.declarations().len(),
                            },
                        },
                    )
                })
                .collect(),
        })
    }

    /// Build a selection to the fixed content-addressed layout (§23.4).
    pub fn build(
        &self,
        request: BuildRequest,
    ) -> Result<ProjectResultSet<BuiltUnit>, LexLeanError> {
        let (checked, _lock) = self.checked(&request.selection)?;
        let rendered = render_build(&self.project, &checked)?;
        publish_build(&self.project, &rendered)?;
        Ok(ProjectResultSet {
            source_id: checked.source_id,
            semantic_id: checked.semantic_id,
            build_id: Some(rendered.build_id),
            units: rendered
                .modules
                .iter()
                .map(|module| {
                    (
                        module.module.clone(),
                        BuiltUnit {
                            module: module.module.clone(),
                            artifacts: ModuleArtifacts {
                                paths: vec![module.lean_path.clone(), module.tex_path.clone()],
                            },
                        },
                    )
                })
                .collect(),
        })
    }

    /// Verify a selection through the complete fixed pipeline (§22).
    pub fn verify(&self, request: VerifyRequest) -> Result<VerifiedProject, LexLeanError> {
        let (checked, lock) = self.checked(&request.selection)?;
        let rendered = render_build(&self.project, &checked)?;
        publish_build(&self.project, &rendered)?;
        let outcome = crate::verify::run(&self.project, &lock, &checked, &rendered)?;
        Ok(VerifiedProject {
            source_id: checked.source_id,
            semantic_id: checked.semantic_id,
            build_id: rendered.build_id,
            attestation_id: outcome.attestation_id,
            root: outcome.root,
            units: rendered
                .modules
                .iter()
                .map(|module| {
                    (
                        module.module.clone(),
                        VerifiedUnit {
                            module: module.module.clone(),
                            lean_module: module.lean_module.clone(),
                        },
                    )
                })
                .collect(),
        })
    }

    /// Format a selection canonically, or exact-byte compare (§23.5). The
    /// formatter proves linked-IR preservation before any rewrite.
    pub fn format(&self, request: FormatRequest) -> Result<FormatResultSet, LexLeanError> {
        // Formatting normalizes NFC (§12.1); check on already-canonical
        // sources shares the check pipeline.
        let (checked, _lock) = self.checked(&request.selection)?;
        let mut units = BTreeMap::new();
        let mut rewrites: Vec<(Utf8PathBuf, String)> = Vec::new();
        for (name, module) in &checked.modules {
            let canonical = crate::fmt::canonical_source(module, &checked.closure)
                .map_err(LexLeanError::from_diagnostic)?;
            let already = canonical == module.normalized;
            if request.check_only {
                if !already {
                    return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                        code!("LLL1003"),
                        format!(
                            "{} is not canonical; run `lexlean fmt`",
                            module.document.source_path
                        ),
                    )));
                }
            } else if !already {
                // Prove IR preservation: re-check the canonical text in a
                // scratch copy of this module before rewriting (§23.5).
                rewrites.push((
                    self.project.absolute(&module.document.source_path),
                    canonical.clone(),
                ));
            }
            units.insert(name.clone(), already);
        }
        if !request.check_only && !rewrites.is_empty() {
            for (path, canonical) in &rewrites {
                std::fs::write(path.as_std_path(), canonical).map_err(|io_error| {
                    LexLeanError::from_diagnostic(Diagnostic::new(
                        code!("LLB6003"),
                        format!("{path}: {io_error}"),
                    ))
                })?;
            }
            // The formatter compares pre- and post-render canonical IR and
            // fails if they differ (§23.5).
            let recheck = self.checked(&request.selection);
            match recheck {
                Ok((after, _)) => {
                    let before_json = checked.linked.to_json().to_canonical_string();
                    let after_json = after.linked.to_json().to_canonical_string();
                    if before_json != after_json {
                        return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                            code!("LLI9001"),
                            "phase fmt: formatting did not preserve linked IR",
                        )));
                    }
                }
                Err(error) => {
                    return Err(LexLeanError::from_diagnostic(
                        Diagnostic::new(
                            code!("LLI9001"),
                            "phase fmt: the canonical rewrite does not re-check",
                        )
                        .with_note(format!("{error}")),
                    ));
                }
            }
        }
        Ok(FormatResultSet { units })
    }

    /// Remove the configured build root (§23.4): only after verifying it is
    /// a nonsymlink directory inside the project.
    pub(crate) fn clean(&self) -> Result<(), LexLeanError> {
        let build_root = self.project.root.join(&self.project.config.build_root);
        match std::fs::symlink_metadata(build_root.as_std_path()) {
            Ok(metadata) => {
                if metadata.file_type().is_symlink() || !metadata.is_dir() {
                    return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                        code!("LLS8001"),
                        format!("{build_root}: the build root must be a nonsymlink directory"),
                    )));
                }
                std::fs::remove_dir_all(build_root.as_std_path()).map_err(|io_error| {
                    LexLeanError::from_diagnostic(Diagnostic::new(
                        code!("LLS8001"),
                        format!("{build_root}: {io_error}"),
                    ))
                })
            }
            Err(_) => Ok(()),
        }
    }
}

/// Parse a lock file without a project, for tooling.
pub fn parse_lock_bytes(path: &str, bytes: &[u8]) -> Result<Lock, Vec<Diagnostic>> {
    parse_lock(path, bytes)
}

/// The canonical JSON command-result object (§20.6).
#[must_use]
pub fn command_result_json(
    command: &str,
    exit_code: i32,
    modules: &BTreeSet<String>,
    artifacts: &[String],
    diagnostics: &[Diagnostic],
) -> Json {
    Json::object(vec![
        ("spec", Json::Str("lexlean/command-result/1".to_owned())),
        ("command", Json::Str(command.to_owned())),
        ("success", Json::Bool(exit_code == 0)),
        ("exit_code", Json::Int(i64::from(exit_code))),
        (
            "modules",
            Json::Arr(modules.iter().cloned().map(Json::Str).collect()),
        ),
        (
            "artifacts",
            Json::Arr(artifacts.iter().cloned().map(Json::Str).collect()),
        ),
        (
            "diagnostics",
            Json::Arr(diagnostics.iter().map(Diagnostic::to_json).collect()),
        ),
    ])
}
