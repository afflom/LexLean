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
        // Output coverage closure is checked mechanically before anything
        // is published (§19.6, §20.5).
        if let Err(reason) =
            crate::backend::check_output_closure(lean_emitter.text(), &coverage.lean)
        {
            return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLB6001"),
                format!("generated Lean for `{name}` has incomplete output coverage: {reason}"),
            )));
        }
        if let Err(reason) =
            crate::backend::check_output_closure(tex_emitter.text(), &coverage.latex)
        {
            return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLB6002"),
                format!("canonical LaTeX for `{name}` has incomplete output coverage: {reason}"),
            )));
        }

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
        // A lexicon input row names where the package came from (§21.6):
        // the configured project-relative path for path packages,
        // `embedded` for builtin packages, and the pinned Git coordinate
        // (`git:<url>#<revision>/<subdirectory>`) otherwise.
        let path = project
            .config
            .lexicon_sources
            .iter()
            .find(|source| source.package() == package.id)
            .map_or_else(
                || "embedded".to_owned(),
                |source| match source {
                    crate::config::LexiconSource::Builtin { .. } => "embedded".to_owned(),
                    crate::config::LexiconSource::Path { path, .. } => path.clone(),
                    crate::config::LexiconSource::Git {
                        url,
                        revision,
                        subdirectory,
                        ..
                    } => format!("git:{url}#{revision}/{subdirectory}"),
                },
            );
        inputs.push(FileRow {
            kind: "lexicon".to_owned(),
            path,
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

/// A host filesystem or platform failure under the project (§23.6 exit 3):
/// never a language error and never blamed on the input.
fn host_failure(message: impl Into<String>) -> LexLeanError {
    LexLeanError::from_diagnostic(Diagnostic::new(code!("LLV7010"), message))
}

/// The held project mutation lock (§21.8). Dropping it releases the lock.
pub(crate) struct MutationGuard {
    _file: std::fs::File,
}

/// Acquire the project mutation lock at `<build_root>/.lock` (§21.8). The
/// build root's components are checked for symlinks first (§25.1).
fn acquire_lock(project: &Project) -> Result<MutationGuard, LexLeanError> {
    use fs4::fs_std::FileExt;
    let build_root = project
        .confined_creatable(&project.config.build_root)
        .map_err(LexLeanError::from_diagnostic)?;
    std::fs::create_dir_all(build_root.as_std_path()).map_err(|io_error| {
        host_failure(format!(
            "{}: cannot create the build root: {io_error}",
            project.config.build_root
        ))
    })?;
    let lock_relative = format!("{}/.lock", project.config.build_root);
    let lock_path = project
        .confined_creatable(&lock_relative)
        .map_err(LexLeanError::from_diagnostic)?;
    let file = std::fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(lock_path.as_std_path())
        .map_err(|io_error| host_failure(format!("{lock_relative}: {io_error}")))?;
    file.lock_exclusive()
        .map_err(|io_error| host_failure(format!("{lock_relative}: {io_error}")))?;
    Ok(MutationGuard { _file: file })
}

/// Publish a rendered build atomically at its content-addressed path
/// (§21.5, §21.8): staging, fsync, validate-before-reuse, rename.
pub fn publish_build(
    project: &Project,
    build: &RenderedBuild,
) -> Result<Utf8PathBuf, LexLeanError> {
    let guard = acquire_lock(project)?;
    publish_build_locked(project, build, &guard)
}

/// [`publish_build`] under an already-held mutation lock, so a caller such
/// as `verify` holds one lock across build publication and verification.
fn publish_build_locked(
    project: &Project,
    build: &RenderedBuild,
    _guard: &MutationGuard,
) -> Result<Utf8PathBuf, LexLeanError> {
    let build_root_relative = format!("{}/build", project.config.build_root);
    let build_root = project
        .confined_creatable(&build_root_relative)
        .map_err(LexLeanError::from_diagnostic)?;
    std::fs::create_dir_all(build_root.as_std_path()).map_err(|io_error| {
        LexLeanError::from_diagnostic(Diagnostic::new(
            code!("LLB6003"),
            format!("{build_root_relative}: {io_error}"),
        ))
    })?;
    let target_relative = format!("{build_root_relative}/{}", build.build_id.to_hex());
    let target = build_root.join(build.build_id.to_hex());
    if std::fs::symlink_metadata(target.as_std_path()).is_ok() {
        // Existing content-addressed output is reused only after every
        // file validates against the new manifest and no extra file is
        // present (§21.8); a symlinked
        // output is never followed (§25.1).
        project
            .confined_dir(&target_relative)
            .map_err(LexLeanError::from_diagnostic)?;
        for (relative, bytes) in &build.files {
            let existing = std::fs::read(target.join(relative).as_std_path());
            match existing {
                Ok(found) if found == *bytes => {}
                _ => {
                    return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                        code!("LLB6003"),
                        format!(
                            "existing build directory {target_relative} does not validate against the manifest at `{relative}`; refusing to overwrite unexplained bytes"
                        ),
                    )));
                }
            }
        }
        let expected: BTreeSet<&str> = build
            .files
            .iter()
            .map(|(relative, _)| relative.as_str())
            .collect();
        for entry in walkdir::WalkDir::new(target.as_std_path())
            .into_iter()
            .flatten()
        {
            if !entry.file_type().is_file() {
                continue;
            }
            let relative = entry
                .path()
                .strip_prefix(target.as_std_path())
                .map(|path| path.to_string_lossy().replace('\\', "/"))
                .unwrap_or_default();
            if !expected.contains(relative.as_str()) {
                return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLB6003"),
                    format!(
                        "existing build directory {target} holds the unexplained extra file `{relative}`; refusing to reuse it"
                    ),
                )));
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
            format!("publishing {target_relative}: {io_error}"),
        ))
    })?;
    crate::artifact::fsync_dir(build_root.as_std_path());
    Ok(target)
}

/// Copy a directory tree (regular files and directories only; symlinks
/// and special files are skipped because every consumer rejects them
/// anyway) for the formatter's scratch project.
fn copy_tree(from: &Utf8Path, to: &Utf8Path, shown: &str) -> Result<(), LexLeanError> {
    for entry in walkdir::WalkDir::new(from.as_std_path())
        .follow_links(false)
        .sort_by_file_name()
    {
        let entry = entry.map_err(|walk_error| {
            host_failure(format!(
                "fmt staging {shown}: {}",
                walk_error
                    .io_error()
                    .map_or_else(|| "walk failure".to_owned(), ToString::to_string)
            ))
        })?;
        let relative = entry.path().strip_prefix(from.as_std_path()).map_err(|_| {
            host_failure(format!("fmt staging {shown}: a walked entry left its root"))
        })?;
        let destination = to.as_std_path().join(relative);
        let file_type = entry.file_type();
        if file_type.is_dir() {
            std::fs::create_dir_all(&destination)
                .map_err(|io_error| host_failure(format!("fmt staging {shown}: {io_error}")))?;
        } else if file_type.is_file() {
            if let Some(parent) = destination.parent() {
                std::fs::create_dir_all(parent)
                    .map_err(|io_error| host_failure(format!("fmt staging {shown}: {io_error}")))?;
            }
            std::fs::copy(entry.path(), &destination)
                .map_err(|io_error| host_failure(format!("fmt staging {shown}: {io_error}")))?;
        }
    }
    Ok(())
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

    /// Enforce `limits.max_diagnostics` on a failure (§10.2).
    fn bound<T>(&self, phase: &str, result: Result<T, LexLeanError>) -> Result<T, LexLeanError> {
        result.map_err(|error| error.bounded(self.project.config.limits.max_diagnostics, phase))
    }

    /// Update or check the lock (§23.4).
    pub fn lock(&self, request: LockRequest) -> Result<LockResult, LexLeanError> {
        self.bound("lock", self.lock_inner(request))
    }

    fn lock_inner(&self, request: LockRequest) -> Result<LockResult, LexLeanError> {
        if request.check_only && request.allow_network {
            return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLC0001"),
                "--check and --allow-network are mutually exclusive",
            )));
        }
        if request.check_only {
            // `lock --check` requires canonical bytes of both the lock and
            // the configuration (§10.1, §11.1); nothing is written.
            let canonical_config = self.project.config.canonical_toml();
            if self.project.config_bytes != canonical_config.as_bytes() {
                return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLC0101"),
                    format!(
                        "{} is not in canonical serialization; `lock --check` requires canonical configuration bytes (§10.1)",
                        self.project.config_name
                    ),
                )));
            }
            let (lock, _packages) =
                compute_lock(&self.project, false).map_err(LexLeanError::from_diagnostics)?;
            let bytes = lock.canonical_bytes();
            let existing = crate::lock::read_lock_bytes(&self.project)
                .map_err(LexLeanError::from_diagnostic)?;
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
        // The whole update, acquisition included, runs under the mutation
        // lock (§21.8).
        let _guard = acquire_lock(&self.project)?;
        let (lock, _packages) = compute_lock(&self.project, request.allow_network)
            .map_err(LexLeanError::from_diagnostics)?;
        let bytes = lock.canonical_bytes();
        let lock_path = self
            .project
            .confined_creatable(&self.project.config.lockfile)
            .map_err(LexLeanError::from_diagnostic)?;
        if std::fs::symlink_metadata(lock_path.as_std_path()).is_ok() {
            let existing = crate::lock::read_lock_bytes(&self.project)
                .map_err(LexLeanError::from_diagnostic)?;
            if existing == bytes {
                return Ok(LockResult {
                    bytes,
                    written: false,
                });
            }
        }
        // Atomic write beside the target with ordinary file permissions.
        let parent = lock_path
            .parent()
            .map(Utf8Path::to_path_buf)
            .unwrap_or_else(|| self.project.root.clone());
        let lockfile = &self.project.config.lockfile;
        let mut temp = tempfile::NamedTempFile::new_in(parent.as_std_path())
            .map_err(|io_error| host_failure(format!("{lockfile}: staging: {io_error}")))?;
        use std::io::Write;
        temp.write_all(&bytes)
            .and_then(|()| temp.as_file().sync_all())
            .map_err(|io_error| host_failure(format!("{lockfile}: staging: {io_error}")))?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(temp.path(), std::fs::Permissions::from_mode(0o644))
                .map_err(|io_error| host_failure(format!("{lockfile}: staging: {io_error}")))?;
        }
        temp.persist(lock_path.as_std_path())
            .map_err(|persist_error| {
                host_failure(format!("{lockfile}: publish: {}", persist_error.error))
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
        self.bound("check", self.check_inner(&request))
    }

    fn check_inner(
        &self,
        request: &CheckRequest,
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
        self.bound("build", self.build_inner(&request))
    }

    fn build_inner(
        &self,
        request: &BuildRequest,
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
        self.bound("verify", self.verify_inner(&request))
    }

    fn verify_inner(&self, request: &VerifyRequest) -> Result<VerifiedProject, LexLeanError> {
        let (checked, lock) = self.checked(&request.selection)?;
        let rendered = render_build(&self.project, &checked)?;
        // One mutation lock spans build publication, every verification
        // stage, and the verified-set publication (§21.8).
        let guard = acquire_lock(&self.project)?;
        publish_build_locked(&self.project, &rendered, &guard)?;
        let outcome = crate::verify::run(&self.project, &lock, &checked, &rendered)?;
        drop(guard);
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
    /// formatter proves linked-IR preservation on the in-memory canonical
    /// text before any source file is touched, then rewrites each file
    /// atomically under the mutation lock.
    pub fn format(&self, request: FormatRequest) -> Result<FormatResultSet, LexLeanError> {
        self.bound("fmt", self.format_inner(&request))
    }

    #[allow(clippy::too_many_lines)]
    fn format_inner(&self, request: &FormatRequest) -> Result<FormatResultSet, LexLeanError> {
        let raw_bytes = |relative: &str| -> Result<Vec<u8>, LexLeanError> {
            let path = self
                .project
                .confined_file(relative)
                .map_err(LexLeanError::from_diagnostic)?;
            std::fs::read(path.as_std_path())
                .map_err(|io_error| host_failure(format!("{relative}: {io_error}")))
        };
        if request.check_only {
            // Exact-byte comparison against the file as it is on disk (§23.5):
            // a CRLF or otherwise noncanonical file is not canonical even
            // when its normalized text is.
            let (checked, _lock) = self.checked(&request.selection)?;
            let mut units = BTreeMap::new();
            for (name, module) in &checked.modules {
                let canonical = crate::fmt::canonical_source(module, &checked.closure)
                    .map_err(LexLeanError::from_diagnostic)?;
                let raw = raw_bytes(&module.document.source_path)?;
                if raw != canonical.as_bytes() {
                    return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                        code!("LLL1003"),
                        format!(
                            "{} is not canonical; run `lexlean fmt`",
                            module.document.source_path
                        ),
                    )));
                }
                units.insert(name.clone(), true);
            }
            return Ok(FormatResultSet { units });
        }

        // Every rewrite happens under the mutation lock (§21.8), and the
        // proof of IR preservation precedes the first write: the project is
        // copied to a scratch root under the build root, every module there
        // is NFC/LF-normalized (the part of formatting that precedes
        // parsing, §23.5), and the scratch copy is checked twice: once as
        // normalized (the "before" IR) and once with the canonical text (the
        // "after" IR).
        let _guard = acquire_lock(&self.project)?;
        let build_root = self
            .project
            .confined_creatable(&self.project.config.build_root)
            .map_err(LexLeanError::from_diagnostic)?;
        let staging = tempfile::Builder::new()
            .prefix(".staging-fmt-")
            .tempdir_in(build_root.as_std_path())
            .map_err(|io_error| host_failure(format!("fmt staging: {io_error}")))?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let _ =
                std::fs::set_permissions(staging.path(), std::fs::Permissions::from_mode(0o700));
        }
        let scratch = crate::project::utf8_path(staging.path())
            .map(|path| path.join("project"))
            .map_err(LexLeanError::from_diagnostic)?;
        self.scratch_project_copy(&scratch)?;
        let scratch_engine = Self::load(&scratch.join(&self.project.config_name))?;
        for relative in scratch_engine
            .project
            .all_modules()
            .map_err(LexLeanError::from_diagnostics)?
            .values()
        {
            let path = scratch.join(relative);
            let bytes = std::fs::read(path.as_std_path())
                .map_err(|io_error| host_failure(format!("fmt staging {relative}: {io_error}")))?;
            let normalized = crate::source::normalize::normalize(relative, &bytes, true)
                .map_err(LexLeanError::from_diagnostics)?;
            std::fs::write(path.as_std_path(), normalized.text)
                .map_err(|io_error| host_failure(format!("fmt staging {relative}: {io_error}")))?;
        }
        let (before, _lock) = scratch_engine.checked(&request.selection)?;
        let mut units = BTreeMap::new();
        let mut rewrites: Vec<(String, String)> = Vec::new();
        for (name, module) in &before.modules {
            let canonical = crate::fmt::canonical_source(module, &before.closure)
                .map_err(LexLeanError::from_diagnostic)?;
            let raw = raw_bytes(&module.document.source_path)?;
            let already = raw == canonical.as_bytes();
            if !already {
                rewrites.push((module.document.source_path.clone(), canonical));
            }
            units.insert(name.clone(), already);
        }
        if rewrites.is_empty() {
            return Ok(FormatResultSet { units });
        }
        for (relative, canonical) in &rewrites {
            std::fs::write(scratch.join(relative).as_std_path(), canonical)
                .map_err(|io_error| host_failure(format!("fmt staging {relative}: {io_error}")))?;
        }
        match scratch_engine.checked(&request.selection) {
            Ok((after, _)) => {
                let before_json = before.linked.to_json().to_canonical_string();
                let after_json = after.linked.to_json().to_canonical_string();
                if before_json != after_json {
                    return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                        code!("LLI9001"),
                        "phase fmt: formatting did not preserve linked IR; no file was rewritten",
                    )));
                }
                // The canonical text must itself be a fixed point.
                for (name, module) in &after.modules {
                    let again = crate::fmt::canonical_source(module, &after.closure)
                        .map_err(LexLeanError::from_diagnostic)?;
                    if again != module.normalized {
                        return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                            code!("LLI9001"),
                            format!(
                                "phase fmt: the canonical text of `{name}` is not a formatting fixed point; no file was rewritten"
                            ),
                        )));
                    }
                }
            }
            Err(error) => {
                return Err(LexLeanError::from_diagnostic(
                    Diagnostic::new(
                        code!("LLI9001"),
                        "phase fmt: the canonical rewrite does not re-check; no file was rewritten",
                    )
                    .with_note(format!("{error}")),
                ));
            }
        }
        drop(scratch_engine);
        drop(staging);

        // Proven: rewrite each file through a sibling temporary and rename.
        for (relative, canonical) in &rewrites {
            let path = self
                .project
                .confined_file(relative)
                .map_err(LexLeanError::from_diagnostic)?;
            let parent = path
                .parent()
                .map(Utf8Path::to_path_buf)
                .unwrap_or_else(|| self.project.root.clone());
            let mut temp = tempfile::NamedTempFile::new_in(parent.as_std_path())
                .map_err(|io_error| host_failure(format!("{relative}: staging: {io_error}")))?;
            use std::io::Write;
            temp.write_all(canonical.as_bytes())
                .and_then(|()| temp.as_file().sync_all())
                .map_err(|io_error| host_failure(format!("{relative}: staging: {io_error}")))?;
            if let Ok(metadata) = std::fs::metadata(path.as_std_path()) {
                let _ = std::fs::set_permissions(temp.path(), metadata.permissions());
            }
            temp.persist(path.as_std_path()).map_err(|persist_error| {
                host_failure(format!("{relative}: publish: {}", persist_error.error))
            })?;
        }
        Ok(FormatResultSet { units })
    }

    /// Copy the inputs of a check (configuration, lock, workspace pins,
    /// source roots, path packages, the Git cache, PDF resources) into a
    /// scratch root so the canonical text can be re-checked without
    /// touching the user's files.
    fn scratch_project_copy(&self, scratch: &Utf8Path) -> Result<(), LexLeanError> {
        let config = &self.project.config;
        std::fs::create_dir_all(scratch.as_std_path())
            .map_err(|io_error| host_failure(format!("fmt staging: {io_error}")))?;
        let copy_file = |relative: &str| -> Result<(), LexLeanError> {
            let source = self.project.absolute(relative);
            if std::fs::symlink_metadata(source.as_std_path())
                .is_ok_and(|metadata| metadata.is_file())
            {
                let destination = scratch.join(relative);
                if let Some(parent) = destination.parent() {
                    std::fs::create_dir_all(parent.as_std_path())
                        .map_err(|io_error| host_failure(format!("{relative}: {io_error}")))?;
                }
                std::fs::copy(source.as_std_path(), destination.as_std_path())
                    .map_err(|io_error| host_failure(format!("{relative}: {io_error}")))?;
            }
            Ok(())
        };
        let copy_dir = |relative: &str| -> Result<(), LexLeanError> {
            let source = self.project.absolute(relative);
            if std::fs::symlink_metadata(source.as_std_path())
                .is_ok_and(|metadata| metadata.is_dir())
            {
                copy_tree(&source, &scratch.join(relative), relative)?;
            }
            Ok(())
        };
        copy_file(&self.project.config_name)?;
        copy_file(&config.lockfile)?;
        let workspace = |name: &str| {
            if config.lean_workspace == "." {
                name.to_owned()
            } else {
                format!("{}/{name}", config.lean_workspace)
            }
        };
        for pin in [
            "lean-toolchain",
            "lakefile.toml",
            "lakefile.lean",
            "lake-manifest.json",
        ] {
            copy_file(&workspace(pin))?;
        }
        for root in &config.source_roots {
            copy_dir(root)?;
        }
        for source in &config.lexicon_sources {
            if let crate::config::LexiconSource::Path { path, .. } = source {
                copy_dir(path)?;
            }
        }
        copy_dir(&format!("{}/cache", config.build_root))?;
        if let Some(pdf) = &config.pdf {
            for resource in &pdf.resources {
                copy_file(resource)?;
            }
        }
        Ok(())
    }

    /// Remove the configured build root (§23.4): only after verifying it is
    /// a nonsymlink directory inside the project whose path has no symlink
    /// component. An absent build root is reported as such.
    pub(crate) fn clean(&self) -> Result<CleanResult, LexLeanError> {
        let relative = &self.project.config.build_root;
        match std::fs::symlink_metadata(self.project.absolute(relative).as_std_path()) {
            Err(io_error) if io_error.kind() == std::io::ErrorKind::NotFound => {
                Ok(CleanResult::Absent)
            }
            Err(io_error) => Err(LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLS8001"),
                format!("{relative}: {io_error}"),
            ))),
            Ok(_) => {
                let build_root = self
                    .project
                    .confined_dir(relative)
                    .map_err(LexLeanError::from_diagnostic)?;
                let removal_failure = |io_error: std::io::Error| {
                    LexLeanError::from_diagnostic(Diagnostic::new(
                        code!("LLS8001"),
                        format!("{relative}: {io_error}"),
                    ))
                };
                // Everything but the mutation lock file goes under the
                // lock (§21.8), so no concurrent build publishes into a
                // directory being torn down; the lock file and the now
                // empty root are removed once the lock is released, which
                // keeps the removal portable to hosts that refuse to
                // delete an open file.
                {
                    let _guard = acquire_lock(&self.project)?;
                    for entry in
                        std::fs::read_dir(build_root.as_std_path()).map_err(removal_failure)?
                    {
                        let entry = entry.map_err(removal_failure)?;
                        if entry.file_name() == ".lock" {
                            continue;
                        }
                        let path = entry.path();
                        let file_type = entry.file_type().map_err(removal_failure)?;
                        if file_type.is_dir() {
                            std::fs::remove_dir_all(&path).map_err(removal_failure)?;
                        } else {
                            std::fs::remove_file(&path).map_err(removal_failure)?;
                        }
                    }
                }
                std::fs::remove_dir_all(build_root.as_std_path()).map_err(removal_failure)?;
                Ok(CleanResult::Removed)
            }
        }
    }
}

/// The outcome of `clean`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CleanResult {
    /// The build root was removed.
    Removed,
    /// There was no build root to remove.
    Absent,
}

/// Parse a lock file without a project, for tooling.
pub fn parse_lock_bytes(path: &str, bytes: &[u8]) -> Result<Lock, Vec<Diagnostic>> {
    parse_lock(path, bytes)
}

/// The content IDs a command may report in its JSON result (§20.6): each
/// is present exactly when the command produced it.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CommandIds {
    /// The source ID.
    pub source_id: Option<Sha256Digest>,
    /// The semantic ID.
    pub semantic_id: Option<Sha256Digest>,
    /// The build ID.
    pub build_id: Option<Sha256Digest>,
    /// The attestation ID.
    pub attestation_id: Option<Sha256Digest>,
}

/// The canonical JSON command-result object (§20.6). Absent IDs are
/// omitted rather than encoded as `null`; `explanation` carries the
/// registered entry text for `explain`.
#[must_use]
pub fn command_result_json(
    command: &str,
    exit_code: i32,
    modules: &BTreeSet<String>,
    artifacts: &[String],
    diagnostics: &[Diagnostic],
    ids: &CommandIds,
    explanation: Option<&str>,
) -> Json {
    let mut fields = vec![
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
    ];
    for (name, id) in [
        ("source_id", ids.source_id),
        ("semantic_id", ids.semantic_id),
        ("build_id", ids.build_id),
        ("attestation_id", ids.attestation_id),
    ] {
        if let Some(id) = id {
            fields.push((name, Json::Str(id.to_hex())));
        }
    }
    if let Some(text) = explanation {
        fields.push(("explanation", Json::Str(text.to_owned())));
    }
    Json::object(fields)
}
