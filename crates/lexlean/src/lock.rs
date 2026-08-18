//! The lock file: package resolution, canonical serialization, and exact
//! checking (SPEC.md §11).

use std::collections::{BTreeMap, BTreeSet};

use camino::{Utf8Path, Utf8PathBuf};
use serde::Deserialize;

use crate::artifact::content_id::Sha256Digest;
use crate::code;
use crate::config::{toml_string, LexiconSource};
use crate::diagnostic::Diagnostic;
use crate::lexicon::package::{
    load_package, toml_comment_at, LexiconPackage, LoadContext, PackageRef,
};
use crate::project::Project;

/// One locked package row (§11.1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockPackage {
    /// The package ID.
    pub id: String,
    /// The exact version.
    pub version: String,
    /// `builtin`, `path`, or `git`.
    pub kind: String,
    /// `embedded`, the configured path, or the Git URL.
    pub source: String,
    /// `compiler-semantics`, `none`, or the exact commit.
    pub revision: String,
    /// The §11.5 tree digest.
    pub tree_sha256: Sha256Digest,
    /// SHA-256 of `lexicon.toml`.
    pub manifest_sha256: Sha256Digest,
    /// Sorted unique `package@version` imports.
    pub imports: Vec<String>,
}

/// A locked PDF provider record (§11.1): it mirrors the configured
/// provider (program, argument vectors, output pattern, hashes) and records
/// the hash of every declared resource.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockPdf {
    /// The configured project-relative executable.
    pub program: String,
    /// The configured executable hash.
    pub program_sha256: Sha256Digest,
    /// The configured version probe argv.
    pub version_argv: Vec<String>,
    /// The configured version-output hash.
    pub version_stdout_sha256: Sha256Digest,
    /// The configured compile argv.
    pub compile_argv: Vec<String>,
    /// The configured output pattern.
    pub output: String,
    /// Hashes of every declared resource, sorted by path.
    pub resources: Vec<(String, Sha256Digest)>,
}

/// The complete lock (§11.1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lock {
    /// The compiler-semantics ID at lock time.
    pub compiler_semantics: Sha256Digest,
    /// SHA-256 of the canonical project configuration.
    pub project_config_sha256: Sha256Digest,
    /// Workspace pin rows sorted by path.
    pub workspace_files: Vec<(String, Sha256Digest)>,
    /// Package rows sorted by `(id, version)`.
    pub packages: Vec<LockPackage>,
    /// The optional PDF record.
    pub pdf: Option<LockPdf>,
}

fn toml_array(values: &[String]) -> String {
    let items: Vec<String> = values.iter().map(|value| toml_string(value)).collect();
    format!("[{}]", items.join(", "))
}

impl Lock {
    /// The canonical lock bytes (§11.2): fixed key order, sorted rows,
    /// lowercase hexadecimal, no comments, one final LF.
    #[must_use]
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = String::new();
        out.push_str(&format!("spec = {}\n", toml_string("lexlean/lock/1")));
        out.push_str(&format!(
            "language = {}\n",
            toml_string(crate::LANGUAGE_VERSION)
        ));
        out.push_str(&format!(
            "compiler_semantics = {}\n",
            toml_string(&self.compiler_semantics.to_hex())
        ));
        out.push_str(&format!(
            "project_config_sha256 = {}\n",
            toml_string(&self.project_config_sha256.to_hex())
        ));
        out.push_str(&format!(
            "lean_toolchain = {}\n",
            toml_string(crate::LEAN_TOOLCHAIN)
        ));
        let mut workspace_files = self.workspace_files.clone();
        workspace_files.sort_by(|a, b| a.0.cmp(&b.0));
        for (path, sha256) in &workspace_files {
            out.push_str("\n[[workspace_file]]\n");
            out.push_str(&format!("path = {}\n", toml_string(path)));
            out.push_str(&format!("sha256 = {}\n", toml_string(&sha256.to_hex())));
        }
        let mut packages = self.packages.clone();
        packages.sort_by(|a, b| (&a.id, &a.version).cmp(&(&b.id, &b.version)));
        for package in &packages {
            out.push_str("\n[[package]]\n");
            out.push_str(&format!("id = {}\n", toml_string(&package.id)));
            out.push_str(&format!("version = {}\n", toml_string(&package.version)));
            out.push_str(&format!("kind = {}\n", toml_string(&package.kind)));
            out.push_str(&format!("source = {}\n", toml_string(&package.source)));
            out.push_str(&format!("revision = {}\n", toml_string(&package.revision)));
            out.push_str(&format!(
                "tree_sha256 = {}\n",
                toml_string(&package.tree_sha256.to_hex())
            ));
            out.push_str(&format!(
                "manifest_sha256 = {}\n",
                toml_string(&package.manifest_sha256.to_hex())
            ));
            let imports: Vec<String> = package.imports.iter().map(|i| toml_string(i)).collect();
            out.push_str(&format!("imports = [{}]\n", imports.join(", ")));
        }
        if let Some(pdf) = &self.pdf {
            out.push_str("\n[pdf]\n");
            out.push_str(&format!("program = {}\n", toml_string(&pdf.program)));
            out.push_str(&format!(
                "program_sha256 = {}\n",
                toml_string(&pdf.program_sha256.to_hex())
            ));
            out.push_str(&format!(
                "version_argv = {}\n",
                toml_array(&pdf.version_argv)
            ));
            out.push_str(&format!(
                "version_stdout_sha256 = {}\n",
                toml_string(&pdf.version_stdout_sha256.to_hex())
            ));
            out.push_str(&format!(
                "compile_argv = {}\n",
                toml_array(&pdf.compile_argv)
            ));
            out.push_str(&format!("output = {}\n", toml_string(&pdf.output)));
            let mut resources = pdf.resources.clone();
            resources.sort_by(|a, b| a.0.cmp(&b.0));
            for (path, sha256) in &resources {
                out.push_str("\n[[pdf.resource]]\n");
                out.push_str(&format!("path = {}\n", toml_string(path)));
                out.push_str(&format!("sha256 = {}\n", toml_string(&sha256.to_hex())));
            }
        }
        out.into_bytes()
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawLock {
    spec: String,
    language: String,
    compiler_semantics: String,
    project_config_sha256: String,
    lean_toolchain: String,
    #[serde(rename = "workspace_file", default)]
    workspace_files: Vec<RawWorkspaceFile>,
    #[serde(rename = "package", default)]
    packages: Vec<RawLockPackage>,
    pdf: Option<RawLockPdf>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawWorkspaceFile {
    path: String,
    sha256: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawLockPackage {
    id: String,
    version: String,
    kind: String,
    source: String,
    revision: String,
    tree_sha256: String,
    manifest_sha256: String,
    imports: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawLockPdf {
    program: String,
    program_sha256: String,
    version_argv: Vec<String>,
    version_stdout_sha256: String,
    compile_argv: Vec<String>,
    output: String,
    #[serde(rename = "resource", default)]
    resources: Vec<RawWorkspaceFile>,
}

fn lock_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLC0102"), message)
}

/// Parse a lock file (§11.1). Structural validation only; staleness against
/// the current configuration is [`read_current_lock`].
pub fn parse_lock(path: &str, bytes: &[u8]) -> Result<Lock, Vec<Diagnostic>> {
    let Ok(text) = std::str::from_utf8(bytes) else {
        return Err(vec![lock_error(format!("{path}: lock is not UTF-8"))]);
    };
    if toml_comment_at(text).is_some() {
        return Err(vec![lock_error(format!(
            "{path}: comments are forbidden in a lock file"
        ))]);
    }
    let raw: RawLock = toml::from_str(text)
        .map_err(|error| vec![lock_error(format!("{path}: invalid lock: {error}"))])?;
    let mut diagnostics = Vec::new();
    if raw.spec != "lexlean/lock/1" {
        diagnostics.push(Diagnostic::new(
            code!("LLC0103"),
            format!("{path}: unsupported lock schema `{}`", raw.spec),
        ));
    }
    if raw.language != crate::LANGUAGE_VERSION {
        diagnostics.push(Diagnostic::new(
            code!("LLC0103"),
            format!("{path}: unsupported lock language `{}`", raw.language),
        ));
    }
    if raw.lean_toolchain != crate::LEAN_TOOLCHAIN {
        diagnostics.push(lock_error(format!(
            "{path}: lock pins `{}`, not the language-1.0 toolchain",
            raw.lean_toolchain
        )));
    }
    let hex =
        |field: &str, value: &str, out: &mut Vec<Diagnostic>| match Sha256Digest::from_hex(value) {
            Ok(digest) => digest,
            Err(reason) => {
                out.push(lock_error(format!("{path}: {field}: {reason}")));
                Sha256Digest([0; 32])
            }
        };
    let compiler_semantics = hex(
        "compiler_semantics",
        &raw.compiler_semantics,
        &mut diagnostics,
    );
    let project_config_sha256 = hex(
        "project_config_sha256",
        &raw.project_config_sha256,
        &mut diagnostics,
    );
    let workspace_files: Vec<(String, Sha256Digest)> = raw
        .workspace_files
        .iter()
        .map(|row| {
            (
                row.path.clone(),
                hex("workspace_file", &row.sha256, &mut diagnostics),
            )
        })
        .collect();
    let mut packages = Vec::new();
    for row in &raw.packages {
        for import in &row.imports {
            if PackageRef::parse(import).is_err() {
                diagnostics.push(lock_error(format!(
                    "{path}: package `{}` has invalid import `{import}`",
                    row.id
                )));
            }
        }
        if !row.imports.windows(2).all(|pair| pair[0] < pair[1]) {
            diagnostics.push(lock_error(format!(
                "{path}: package `{}` imports are not sorted and unique",
                row.id
            )));
        }
        packages.push(LockPackage {
            id: row.id.clone(),
            version: row.version.clone(),
            kind: row.kind.clone(),
            source: row.source.clone(),
            revision: row.revision.clone(),
            tree_sha256: hex("tree_sha256", &row.tree_sha256, &mut diagnostics),
            manifest_sha256: hex("manifest_sha256", &row.manifest_sha256, &mut diagnostics),
            imports: row.imports.clone(),
        });
    }
    // §11.3: every package appears exactly once in the lock. A lock naming
    // one package ID twice is rejected as a lock, not carried into the
    // closure for the loader to reject there (§13.11).
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for row in &raw.packages {
        if !seen.insert(row.id.as_str()) {
            diagnostics.push(duplicate(format!(
                "{path}: duplicate package `{}`: every package appears exactly once in the lock",
                row.id
            )));
        }
    }
    let pdf = raw.pdf.as_ref().map(|raw_pdf| LockPdf {
        program: raw_pdf.program.clone(),
        version_argv: raw_pdf.version_argv.clone(),
        compile_argv: raw_pdf.compile_argv.clone(),
        output: raw_pdf.output.clone(),
        program_sha256: hex(
            "pdf.program_sha256",
            &raw_pdf.program_sha256,
            &mut diagnostics,
        ),
        version_stdout_sha256: hex(
            "pdf.version_stdout_sha256",
            &raw_pdf.version_stdout_sha256,
            &mut diagnostics,
        ),
        resources: raw_pdf
            .resources
            .iter()
            .map(|row| {
                (
                    row.path.clone(),
                    hex("pdf.resource", &row.sha256, &mut diagnostics),
                )
            })
            .collect(),
    });
    let lock = Lock {
        compiler_semantics,
        project_config_sha256,
        workspace_files,
        packages,
        pdf,
    };
    if diagnostics.is_empty() {
        Ok(lock)
    } else {
        Err(diagnostics)
    }
}

fn security(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLS8001"), message)
}

fn resolution(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLR3001"), message)
}

/// A duplicate-identity failure in the configured closure (§11.3, §13.11).
fn duplicate(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLR3002"), message)
}

/// Walk `relative` beneath `base` with `symlink_metadata`, rejecting any
/// symlink component and requiring the final component to be a directory.
/// `display_base` names the base in diagnostics (project-relative).
fn confined_dir_under(
    base: &Utf8Path,
    relative: &str,
    display_base: &str,
) -> Result<Utf8PathBuf, Diagnostic> {
    if !crate::config::is_project_relative(relative) {
        return Err(security(format!(
            "`{relative}` is not a relative path beneath `{display_base}`"
        )));
    }
    let mut current = base.to_path_buf();
    let mut walked = display_base.to_owned();
    for segment in relative.split('/') {
        current.push(segment);
        walked.push('/');
        walked.push_str(segment);
        let metadata = std::fs::symlink_metadata(&current)
            .map_err(|io_error| resolution(format!("`{walked}`: {io_error}")))?;
        if metadata.file_type().is_symlink() {
            return Err(security(format!(
                "`{walked}`: symlinks are rejected in lexicon package paths"
            )));
        }
    }
    let metadata = std::fs::symlink_metadata(&current)
        .map_err(|io_error| resolution(format!("`{walked}`: {io_error}")))?;
    if !metadata.is_dir() {
        return Err(security(format!("`{walked}`: expected a directory")));
    }
    Ok(current)
}

/// Collect the participating files of a lexicon package rooted at the
/// already-confined directory `root`: `lexicon.toml` and regular files
/// under `entries/`, rejecting symlinks, special files, and non-UTF-8 paths
/// (§11.5, §25.1). `display_root` names the package root in diagnostics.
pub fn collect_package_files(
    root: &Utf8Path,
    display_root: &str,
) -> Result<Vec<(String, Vec<u8>)>, Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    let mut files: Vec<(String, Vec<u8>)> = Vec::new();
    let display = |absolute: &std::path::Path| -> String {
        match absolute.strip_prefix(root.as_std_path()) {
            Ok(inside) => format!("{display_root}/{}", inside.to_string_lossy()),
            Err(_) => absolute.to_string_lossy().into_owned(),
        }
    };
    let manifest = root.join("lexicon.toml");
    match std::fs::symlink_metadata(&manifest) {
        Ok(metadata) if metadata.is_file() && !metadata.file_type().is_symlink() => {
            match std::fs::read(&manifest) {
                Ok(bytes) => files.push(("lexicon.toml".to_owned(), bytes)),
                Err(io_error) => {
                    diagnostics.push(resolution(format!(
                        "{display_root}/lexicon.toml: {io_error}"
                    )));
                }
            }
        }
        Ok(_) => diagnostics.push(security(format!(
            "{display_root}/lexicon.toml: must be a regular nonsymlink file"
        ))),
        Err(io_error) => {
            diagnostics.push(resolution(format!(
                "{display_root}/lexicon.toml: {io_error}"
            )));
        }
    }
    let entries = root.join("entries");
    if std::fs::symlink_metadata(entries.as_std_path()).is_ok() {
        for entry in walkdir::WalkDir::new(entries.as_std_path())
            .follow_links(false)
            .sort_by_file_name()
        {
            let entry = match entry {
                Ok(entry) => entry,
                Err(walk_error) => {
                    diagnostics.push(resolution(format!("{display_root}/entries: {walk_error}")));
                    continue;
                }
            };
            let file_type = entry.file_type();
            if file_type.is_symlink() {
                diagnostics.push(security(format!(
                    "{}: symlinks are rejected",
                    display(entry.path())
                )));
                continue;
            }
            if file_type.is_dir() {
                continue;
            }
            if !file_type.is_file() {
                diagnostics.push(security(format!(
                    "{}: special files are rejected",
                    display(entry.path())
                )));
                continue;
            }
            let Ok(path) = Utf8PathBuf::from_path_buf(entry.path().to_path_buf()) else {
                diagnostics.push(crate::project::non_utf8_path(entry.path()));
                continue;
            };
            // The digested name is the project-relative spelling, not the
            // host's rendering of it: a package hashes to the same digest on
            // every supported host (§8.3, §11).
            let relative = path
                .strip_prefix(root)
                .map(|p| crate::project::project_relative(p.as_str()))
                .unwrap_or_else(|_| path.to_string());
            match std::fs::read(&path) {
                Ok(bytes) => files.push((relative, bytes)),
                Err(io_error) => {
                    diagnostics.push(resolution(format!("{}: {io_error}", display(entry.path()))))
                }
            }
        }
    }
    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }
    files.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    Ok(files)
}

/// The result of package resolution: every loaded package and its lock row.
pub struct ResolvedPackages {
    /// Loaded packages.
    pub packages: Vec<LexiconPackage>,
    /// Their lock rows.
    pub rows: Vec<LockPackage>,
}

/// Resolve every configured lexicon source plus `lexlean.core` from local
/// and cached sources only (§11.4). `allow_network` additionally permits
/// acquiring a missing exact Git commit.
#[allow(clippy::too_many_lines)]
pub fn resolve_packages(
    project: &Project,
    allow_network: bool,
) -> Result<ResolvedPackages, Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    let mut packages = Vec::new();
    let mut rows = Vec::new();

    let bootstrap = crate::lexicon::load_bootstrap().map_err(|d| vec![d])?;
    let load_ctx = LoadContext {
        forbidden_controls: &bootstrap.structural.forbidden_controls,
        max_scope_depth: project.config.limits.max_scope_depth,
    };

    // Builtins: always the unconditional packages, plus every configured
    // builtin source. Which packages are unconditional is bootstrap data, not a
    // literal here, so a package cannot be locked into every project without
    // also being visible in every module (§14.3).
    let mut builtin_ids: Vec<String> = bootstrap.unconditional_packages();
    for source in &project.config.lexicon_sources {
        if let LexiconSource::Builtin { package } = source {
            if !builtin_ids.contains(package) {
                builtin_ids.push(package.clone());
            }
        }
    }
    for id in &builtin_ids {
        let Some(row) = bootstrap
            .builtin_packages
            .iter()
            .find(|candidate| candidate.id == *id)
        else {
            diagnostics.push(resolution(format!("`{id}` is not a builtin package")));
            continue;
        };
        match crate::lexicon::load_builtin_package(row, &load_ctx) {
            Ok(package) => {
                rows.push(LockPackage {
                    id: package.id.clone(),
                    version: package.version.clone(),
                    kind: "builtin".to_owned(),
                    source: "embedded".to_owned(),
                    revision: "compiler-semantics".to_owned(),
                    tree_sha256: package.tree_sha256,
                    manifest_sha256: package.manifest_sha256,
                    imports: package.imports.iter().map(ToString::to_string).collect(),
                });
                packages.push(package);
            }
            Err(mut package_diagnostics) => diagnostics.append(&mut package_diagnostics),
        }
    }

    for source in &project.config.lexicon_sources {
        // `lexlean.core` is embedded: the compiler carries its exact bytes
        // and digest, and the lock must identify that digest (§12.3). A path
        // or Git source claiming the same package ID would supply a second,
        // foreign `lexlean.core` --- and with it the `is_core` privileges of
        // §13.5 --- so it never reaches the loader.
        if let LexiconSource::Path { package, .. } | LexiconSource::Git { package, .. } = source {
            if package == "lexlean.core" {
                diagnostics.push(duplicate(
                    "duplicate package `lexlean.core`: it is the embedded bootstrap package, which no path or git lexicon_source may supply".to_owned(),
                ));
                continue;
            }
        }
        match source {
            LexiconSource::Builtin { .. } => {}
            LexiconSource::Path { package: id, path } => {
                // A missing package root is a resolution failure; a present
                // one has every component checked (§25.1).
                if std::fs::symlink_metadata(project.absolute(path).as_std_path())
                    .is_err_and(|io_error| io_error.kind() == std::io::ErrorKind::NotFound)
                {
                    diagnostics.push(resolution(format!(
                        "lexicon_source `{id}`: the path package `{path}` does not exist"
                    )));
                    continue;
                }
                let root = match project.confined_dir(path) {
                    Ok(root) => root,
                    Err(diagnostic) => {
                        diagnostics.push(diagnostic);
                        continue;
                    }
                };
                match collect_package_files(&root, path) {
                    Ok(files) => match load_package(path, &files, None, &load_ctx) {
                        Ok(package) => {
                            if package.id != *id {
                                diagnostics.push(resolution(format!(
                                    "`{path}` contains `{}`, not the configured `{id}`",
                                    package.id
                                )));
                                continue;
                            }
                            rows.push(LockPackage {
                                id: package.id.clone(),
                                version: package.version.clone(),
                                kind: "path".to_owned(),
                                source: path.clone(),
                                revision: "none".to_owned(),
                                tree_sha256: package.tree_sha256,
                                manifest_sha256: package.manifest_sha256,
                                imports: package.imports.iter().map(ToString::to_string).collect(),
                            });
                            packages.push(package);
                        }
                        Err(mut package_diagnostics) => {
                            diagnostics.append(&mut package_diagnostics);
                        }
                    },
                    Err(mut file_diagnostics) => diagnostics.append(&mut file_diagnostics),
                }
            }
            LexiconSource::Git {
                package: id,
                url,
                revision,
                subdirectory,
            } => {
                match resolve_git_package(
                    project,
                    id,
                    url,
                    revision,
                    subdirectory,
                    allow_network,
                    &load_ctx,
                ) {
                    Ok(package) => {
                        rows.push(LockPackage {
                            id: package.id.clone(),
                            version: package.version.clone(),
                            kind: "git".to_owned(),
                            source: url.clone(),
                            revision: revision.clone(),
                            tree_sha256: package.tree_sha256,
                            manifest_sha256: package.manifest_sha256,
                            imports: package.imports.iter().map(ToString::to_string).collect(),
                        });
                        packages.push(package);
                    }
                    Err(mut git_diagnostics) => diagnostics.append(&mut git_diagnostics),
                }
            }
        }
    }

    // Every package appears exactly once in the lock (§11.3), and loading a
    // closure with duplicate package IDs is refused (§13.11). Both are
    // decided here, where the lock is computed, so a lock the compiler wrote
    // is never one the compiler refuses to load.
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for row in &rows {
        if !seen.insert(row.id.as_str()) {
            diagnostics.push(duplicate(format!(
                "duplicate package `{}`: it is resolved by more than one lexicon source",
                row.id
            )));
        }
    }

    if diagnostics.is_empty() {
        Ok(ResolvedPackages { packages, rows })
    } else {
        Err(diagnostics)
    }
}

/// The project-relative cache directory for one exact commit (§11.4).
fn git_cache_relative(project: &Project, revision: &str) -> String {
    format!("{}/cache/git/{revision}", project.config.build_root)
}

/// Resolve one Git package from the cache, acquiring it over HTTPS only
/// when `allow_network` (§11.4, §25.3). Cached candidates are revalidated
/// (confined, re-digested, identity-checked) before use.
fn resolve_git_package(
    project: &Project,
    id: &str,
    url: &str,
    revision: &str,
    subdirectory: &str,
    allow_network: bool,
    load_ctx: &LoadContext<'_>,
) -> Result<LexiconPackage, Vec<Diagnostic>> {
    let cache_relative = git_cache_relative(project, revision);
    if let Ok(cache_base) = project.confined_dir(&cache_relative) {
        let mut names: Vec<String> = std::fs::read_dir(cache_base.as_std_path())
            .into_iter()
            .flatten()
            .flatten()
            .filter_map(|entry| entry.file_name().into_string().ok())
            .collect();
        names.sort();
        for name in names {
            let candidate_relative = format!("{cache_relative}/{name}");
            let Ok(candidate) = project.confined_dir(&candidate_relative) else {
                continue;
            };
            if let Ok(files) = collect_package_files(&candidate, &candidate_relative) {
                if let Ok(package) = load_package(&candidate_relative, &files, None, load_ctx) {
                    if package.id == id && name == package.tree_sha256.to_hex() {
                        return Ok(package);
                    }
                }
            }
        }
    }
    if !allow_network {
        // Acquiring the commit would need the network, which only
        // `lock --allow-network` permits (§25.3, I15).
        return Err(vec![Diagnostic::new(
            code!("LLS8003"),
            format!(
                "git package `{id}` at {revision} is not cached and acquiring it needs the network; run `lexlean lock --allow-network`"
            ),
        )]);
    }
    acquire_git_package(project, id, url, revision, subdirectory, load_ctx)
}

/// A Git acquisition failure in the environment (§23.6 exit 3): the
/// executable cannot be run or the exact commit cannot be fetched.
fn git_environment(step: &str, detail: impl std::fmt::Display) -> Vec<Diagnostic> {
    vec![Diagnostic::new(
        code!("LLV7009"),
        format!("git acquisition failed at {step}: {detail}"),
    )]
}

/// Does a `.gitattributes` text enable the LFS filter for any pattern?
/// Attribute lines are `pattern attr...`; the attribute token is exactly
/// `filter=lfs`.
fn gitattributes_enable_lfs(text: &str) -> bool {
    text.lines().any(|line| {
        let line = line.split('#').next().unwrap_or("");
        line.split_whitespace()
            .skip(1)
            .any(|token| token == "filter=lfs")
    })
}

/// The Git LFS pointer-file signature (§11.4): a pointer begins with the
/// spec version line.
const LFS_POINTER_PREFIX: &[u8] = b"version https://git-lfs.github.com/spec/";

/// Scan the whole checkout for submodule, LFS, and nested-repository
/// indirection (§11.4): `.gitmodules` anywhere, an LFS-enabling
/// `.gitattributes` anywhere, an LFS pointer file under the package, or a
/// `.git` entry beneath the checkout root.
fn reject_git_indirection(
    id: &str,
    checkout: &Utf8Path,
    package_root: &Utf8Path,
) -> Result<(), Vec<Diagnostic>> {
    let reject = |what: &str, at: &std::path::Path| -> Vec<Diagnostic> {
        vec![resolution(format!(
            "git package `{id}`: {what} are rejected (found at {})",
            at.strip_prefix(checkout.as_std_path())
                .unwrap_or(at)
                .to_string_lossy()
        ))]
    };
    for entry in walkdir::WalkDir::new(checkout.as_std_path())
        .follow_links(false)
        .sort_by_file_name()
        .into_iter()
        .filter_entry(|entry| {
            // The checkout's own repository metadata is skipped; a nested
            // `.git` deeper down is exactly what must be found.
            !(entry.depth() == 1 && entry.file_name() == ".git")
        })
    {
        let entry = entry.map_err(|walk_error| git_environment("scan", walk_error))?;
        let name = entry.file_name().to_string_lossy();
        if name == ".git" {
            return Err(reject("nested repositories", entry.path()));
        }
        if name == ".gitmodules" {
            return Err(reject("submodules", entry.path()));
        }
        if name == ".gitattributes" && entry.file_type().is_file() {
            if let Ok(text) = std::fs::read_to_string(entry.path()) {
                if gitattributes_enable_lfs(&text) {
                    return Err(reject("LFS indirection", entry.path()));
                }
            }
        }
        if entry.file_type().is_file() && entry.path().starts_with(package_root.as_std_path()) {
            let mut head = vec![0u8; LFS_POINTER_PREFIX.len()];
            if let Ok(mut file) = std::fs::File::open(entry.path()) {
                use std::io::Read;
                let mut filled = 0usize;
                while filled < head.len() {
                    match file.read(&mut head[filled..]) {
                        Ok(0) | Err(_) => break,
                        Ok(read) => filled = filled.saturating_add(read),
                    }
                }
                if filled == head.len() && head == LFS_POINTER_PREFIX {
                    return Err(reject("LFS pointer files", entry.path()));
                }
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn acquire_git_package(
    project: &Project,
    id: &str,
    url: &str,
    revision: &str,
    subdirectory: &str,
    load_ctx: &LoadContext<'_>,
) -> Result<LexiconPackage, Vec<Diagnostic>> {
    use crate::verify::child::{resolve_on_path, ChildSpec, Normalizer};

    // The build root is created first and every staging byte lands under
    // it, never in the project root (§25.6).
    let build_root = project
        .confined_creatable(&project.config.build_root)
        .map_err(|d| vec![d])?;
    std::fs::create_dir_all(build_root.as_std_path())
        .map_err(|io_error| git_environment("staging", io_error))?;
    let staging = tempfile::Builder::new()
        .prefix(".staging-git-")
        .tempdir_in(build_root.as_std_path())
        .map_err(|io_error| git_environment("staging", io_error))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = std::fs::set_permissions(staging.path(), std::fs::Permissions::from_mode(0o700));
    }
    let staging_utf8 = Utf8PathBuf::from_path_buf(staging.path().to_path_buf())
        .map_err(|bad| vec![crate::project::non_utf8_path(&bad)])?;
    let checkout = staging_utf8.join("checkout");
    std::fs::create_dir_all(checkout.as_std_path())
        .map_err(|io_error| git_environment("staging", io_error))?;

    // Explicit executable resolution, recorded by digest (§25.2), through
    // the shared child runner: cleared allow-list environment, prompts
    // disabled, no askpass helper, no SSH command, checked limits.
    let git = resolve_on_path("git").map_err(|_| {
        git_environment(
            "resolve",
            "no `git` executable is available on PATH; `lock --allow-network` needs one",
        )
    })?;
    let git_sha256 = Sha256Digest::of(
        &std::fs::read(git.as_std_path())
            .map_err(|io_error| git_environment("resolve", io_error))?,
    );
    let git_bin = git
        .parent()
        .map(Utf8Path::to_path_buf)
        .unwrap_or_else(|| project.root.clone());
    let normalizer = Normalizer::new(&staging_utf8, &project.root, &project.root, &staging_utf8);
    let limits = project.config.limits;
    let run_git =
        |arguments: &[&str]| -> Result<crate::verify::child::ChildRecord, Vec<Diagnostic>> {
            let record = crate::verify::child::run(
                &ChildSpec {
                    tool: "git",
                    module: Some(format!("lock:{id}")),
                    program: &git,
                    executable_sha256: git_sha256,
                    argv: arguments.iter().map(|a| (*a).to_owned()).collect(),
                    cwd: &checkout,
                    extra_env: vec![("GIT_ASKPASS".to_owned(), String::new())],
                    home: crate::verify::child::ChildHome::Toolchain {
                        toolchain_bin: &git_bin,
                    },
                },
                &limits,
                &normalizer,
            )
            .map_err(|d| vec![d])?;
            if record.exit_code == 0 {
                Ok(record)
            } else {
                Err(git_environment(
                    arguments.first().copied().unwrap_or("git"),
                    format!("exit {}: {}", record.exit_code, record.stderr.trim_end()),
                ))
            }
        };
    run_git(&["init", "--quiet", "."])?;
    run_git(&["remote", "add", "origin", url])?;
    if run_git(&["fetch", "--quiet", "--depth", "1", "origin", revision]).is_err() {
        // Some servers refuse direct SHA fetches; fall back to a full fetch.
        run_git(&["fetch", "--quiet", "origin"])?;
    }
    run_git(&["checkout", "--quiet", "--detach", revision])?;

    // Submodules are gitlinks (mode 160000) in the index (§11.4).
    let index = run_git(&["ls-files", "-s"])?;
    if index.stdout.lines().any(|line| line.starts_with("160000 ")) {
        return Err(vec![resolution(format!(
            "git package `{id}`: submodules are rejected (a gitlink entry is in the index)"
        ))]);
    }
    let package_root =
        confined_dir_under(&checkout, subdirectory, "checkout").map_err(|d| vec![d])?;
    reject_git_indirection(id, &checkout, &package_root)?;

    let display_root = format!("git:{id}");
    let files = collect_package_files(&package_root, &display_root)?;
    let package = load_package(&display_root, &files, None, load_ctx)?;
    if package.id != id {
        return Err(vec![resolution(format!(
            "git source contains `{}`, not the configured `{id}`",
            package.id
        ))]);
    }

    // The cache directory is staged beside its final location and renamed
    // into place, so a reader never observes a partial package (§21.8).
    let cache_relative = git_cache_relative(project, revision);
    let cache_base = project
        .confined_creatable(&cache_relative)
        .map_err(|d| vec![d])?;
    std::fs::create_dir_all(cache_base.as_std_path())
        .map_err(|io_error| git_environment("cache", io_error))?;
    let cache_staging = tempfile::Builder::new()
        .prefix(".staging-")
        .tempdir_in(cache_base.as_std_path())
        .map_err(|io_error| git_environment("cache", io_error))?;
    for (relative, bytes) in &files {
        let destination = cache_staging.path().join(relative);
        if let Some(parent) = destination.parent() {
            std::fs::create_dir_all(parent)
                .map_err(|io_error| git_environment("cache", io_error))?;
        }
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&destination)
            .map_err(|io_error| git_environment("cache", io_error))?;
        use std::io::Write;
        file.write_all(bytes)
            .and_then(|()| file.sync_all())
            .map_err(|io_error| git_environment("cache", io_error))?;
    }
    let cache_dir = cache_base.join(package.tree_sha256.to_hex());
    let staged = cache_staging.keep();
    if let Err(io_error) = std::fs::rename(&staged, cache_dir.as_std_path()) {
        let _ = std::fs::remove_dir_all(&staged);
        // A concurrent acquisition may have published the same content;
        // that is only acceptable when it validates.
        let cache_dir_relative = format!("{cache_relative}/{}", package.tree_sha256.to_hex());
        let existing = project.confined_dir(&cache_dir_relative).and_then(|dir| {
            collect_package_files(&dir, &cache_dir_relative).map_err(|mut d| {
                d.pop()
                    .unwrap_or_else(|| resolution("cache validation failed"))
            })
        });
        match existing {
            Ok(existing_files) if existing_files == files => {}
            _ => return Err(git_environment("cache", io_error)),
        }
    }
    Ok(package)
}

/// Read one workspace pin candidate: `Ok(None)` when absent, the bytes when
/// it is a confined regular file, and a diagnostic for a symlink or
/// special file (§25.1).
fn pin_candidate(project: &Project, relative: &str) -> Result<Option<Vec<u8>>, Diagnostic> {
    match std::fs::symlink_metadata(project.absolute(relative).as_std_path()) {
        Err(io_error) if io_error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(io_error) => Err(Diagnostic::new(
            code!("LLC0101"),
            format!("{relative}: {io_error}"),
        )),
        Ok(_) => {
            let absolute = project.confined_file_or_missing(relative, || {
                Diagnostic::new(
                    code!("LLV7007"),
                    format!("the Lake workspace has no `{relative}`"),
                )
            })?;
            std::fs::read(absolute.as_std_path())
                .map(Some)
                .map_err(|io_error| {
                    Diagnostic::new(code!("LLC0101"), format!("{relative}: {io_error}"))
                })
        }
    }
}

/// Compute the workspace pin rows (§10.4): `lean-toolchain` (whose trimmed
/// content must be the exact pinned string), exactly one Lake
/// configuration, and `lake-manifest.json` when present. Every pinned file
/// is confined: no symlink component (§25.1).
pub fn workspace_pins(project: &Project) -> Result<Vec<(String, Sha256Digest)>, Vec<Diagnostic>> {
    let workspace_relative = |name: &str| {
        if project.config.lean_workspace == "." {
            name.to_owned()
        } else {
            format!("{}/{name}", project.config.lean_workspace)
        }
    };
    let mut diagnostics = Vec::new();
    let mut rows = Vec::new();

    let toolchain_relative = workspace_relative("lean-toolchain");
    match project.confined_file_or_missing(&toolchain_relative, || {
        Diagnostic::new(
            code!("LLV7007"),
            format!(
                "the Lake workspace has no `{toolchain_relative}`; language 1.0 pins {}",
                crate::LEAN_TOOLCHAIN
            ),
        )
    }) {
        Ok(absolute) => match std::fs::read(absolute.as_std_path()) {
            Ok(bytes) => {
                let content = String::from_utf8_lossy(&bytes);
                if content.trim() != crate::LEAN_TOOLCHAIN {
                    diagnostics.push(Diagnostic::new(
                        code!("LLC0101"),
                        format!(
                            "{toolchain_relative} pins `{}`, not the exact language-1.0 toolchain `{}`",
                            content.trim(),
                            crate::LEAN_TOOLCHAIN
                        ),
                    ));
                }
                rows.push((toolchain_relative.clone(), Sha256Digest::of(&bytes)));
            }
            Err(io_error) => diagnostics.push(Diagnostic::new(
                code!("LLC0101"),
                format!("{toolchain_relative}: {io_error}"),
            )),
        },
        Err(diagnostic) => diagnostics.push(diagnostic),
    }

    let lakefile_toml = workspace_relative("lakefile.toml");
    let lakefile_lean = workspace_relative("lakefile.lean");
    let toml_bytes = pin_candidate(project, &lakefile_toml);
    let lean_bytes = pin_candidate(project, &lakefile_lean);
    match (toml_bytes, lean_bytes) {
        (Err(diagnostic), _) | (_, Err(diagnostic)) => diagnostics.push(diagnostic),
        (Ok(Some(_)), Ok(Some(_))) => diagnostics.push(Diagnostic::new(
            code!("LLC0101"),
            "the Lake workspace must contain exactly one Lake configuration; both lakefile.toml and lakefile.lean exist",
        )),
        (Ok(None), Ok(None)) => diagnostics.push(Diagnostic::new(
            code!("LLC0101"),
            "the Lake workspace has no lakefile.toml or lakefile.lean",
        )),
        (Ok(Some(bytes)), Ok(None)) => rows.push((lakefile_toml, Sha256Digest::of(&bytes))),
        (Ok(None), Ok(Some(bytes))) => rows.push((lakefile_lean, Sha256Digest::of(&bytes))),
    }

    let manifest = workspace_relative("lake-manifest.json");
    match pin_candidate(project, &manifest) {
        Ok(Some(bytes)) => rows.push((manifest, Sha256Digest::of(&bytes))),
        Ok(None) => {}
        Err(diagnostic) => diagnostics.push(diagnostic),
    }
    if diagnostics.is_empty() {
        Ok(rows)
    } else {
        Err(diagnostics)
    }
}

/// Compute the complete lock for a project (§11).
pub fn compute_lock(
    project: &Project,
    allow_network: bool,
) -> Result<(Lock, Vec<LexiconPackage>), Vec<Diagnostic>> {
    let resolved = resolve_packages(project, allow_network)?;

    // The closure must include every transitive import exactly once (§11.3);
    // imports of loaded packages must all be loaded.
    let loaded: BTreeMap<&str, &LexiconPackage> = resolved
        .packages
        .iter()
        .map(|package| (package.id.as_str(), package))
        .collect();
    let mut diagnostics = Vec::new();
    for package in &resolved.packages {
        for import in &package.imports {
            match loaded.get(import.package.as_str()) {
                Some(target) if target.version == import.version => {}
                _ => diagnostics.push(resolution(format!(
                    "{}: transitive import `{import}` is not part of the configured closure",
                    package.id
                ))),
            }
        }
    }
    let workspace_files = match workspace_pins(project) {
        Ok(rows) => rows,
        Err(mut pin_diagnostics) => {
            diagnostics.append(&mut pin_diagnostics);
            Vec::new()
        }
    };
    let pdf = project.config.pdf.as_ref().map(|provider| {
        let resources = provider
            .resources
            .iter()
            .filter_map(|resource| {
                match project.confined_file(resource).and_then(|absolute| {
                    std::fs::read(absolute.as_std_path()).map_err(|io_error| {
                        Diagnostic::new(code!("LLC0101"), format!("{resource}: {io_error}"))
                    })
                }) {
                    Ok(bytes) => Some((resource.clone(), Sha256Digest::of(&bytes))),
                    Err(diagnostic) => {
                        diagnostics.push(diagnostic);
                        None
                    }
                }
            })
            .collect();
        LockPdf {
            program: provider.program.clone(),
            program_sha256: provider.program_sha256,
            version_argv: provider.version_argv.clone(),
            version_stdout_sha256: provider.version_stdout_sha256,
            compile_argv: provider.compile_argv.clone(),
            output: provider.output.clone(),
            resources,
        }
    });
    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }
    Ok((
        Lock {
            compiler_semantics: crate::compiler_semantics_id(),
            project_config_sha256: project.config.config_sha256(),
            workspace_files,
            packages: resolved.rows,
            pdf,
        },
        resolved.packages,
    ))
}

/// Read the committed lock bytes through the confined lock path (§25.1):
/// no symlink component, a regular file.
pub fn read_lock_bytes(project: &Project) -> Result<Vec<u8>, Diagnostic> {
    let lock_path = project.confined_file_or_missing(&project.config.lockfile, || {
        lock_error(format!(
            "{} does not exist; run `lexlean lock`",
            project.config.lockfile
        ))
    })?;
    std::fs::read(lock_path.as_std_path()).map_err(|io_error| {
        lock_error(format!(
            "{}: {io_error}; run `lexlean lock`",
            project.config.lockfile
        ))
    })
}

/// Read the committed lock and require it to be current: canonical bytes,
/// matching compiler semantics, matching project configuration, and
/// matching package digests (§11, CF-10).
pub fn read_current_lock(
    project: &Project,
) -> Result<(Lock, Vec<LexiconPackage>), Vec<Diagnostic>> {
    let bytes = read_lock_bytes(project).map_err(|d| vec![d])?;
    let committed = parse_lock(&project.config.lockfile, &bytes)?;
    let (expected, packages) = compute_lock(project, false)?;
    if expected.canonical_bytes() != bytes {
        let mut mismatch = lock_error(format!(
            "{} is stale or noncanonical; run `lexlean lock`",
            project.config.lockfile
        ));
        if committed.project_config_sha256 != expected.project_config_sha256 {
            mismatch = mismatch.with_note("the project configuration changed since locking");
        }
        if committed.compiler_semantics != expected.compiler_semantics {
            mismatch = mismatch.with_note("the compiler semantics changed since locking");
        }
        return Err(vec![mismatch]);
    }
    Ok((committed, packages))
}
