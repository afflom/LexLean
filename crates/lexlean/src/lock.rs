//! The lock file: package resolution, canonical serialization, and exact
//! checking (SPEC.md §11).

use std::collections::BTreeMap;

use camino::{Utf8Path, Utf8PathBuf};
use serde::Deserialize;

use crate::artifact::content_id::Sha256Digest;
use crate::code;
use crate::config::LexiconSource;
use crate::diagnostic::Diagnostic;
use crate::lexicon::package::{load_package, toml_comment_at, LexiconPackage, PackageRef};
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

/// A locked PDF provider record (§11.1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockPdf {
    /// The configured executable hash.
    pub program_sha256: Sha256Digest,
    /// The configured version-output hash.
    pub version_stdout_sha256: Sha256Digest,
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

fn toml_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for scalar in value.chars() {
        match scalar {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04X}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
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
            out.push_str(&format!(
                "program_sha256 = {}\n",
                toml_string(&pdf.program_sha256.to_hex())
            ));
            out.push_str(&format!(
                "version_stdout_sha256 = {}\n",
                toml_string(&pdf.version_stdout_sha256.to_hex())
            ));
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
    program_sha256: String,
    version_stdout_sha256: String,
    #[serde(rename = "resource", default)]
    resources: Vec<RawWorkspaceFile>,
}

fn lock_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLC0102"), message)
}

/// Parse a lock file (§11.1). Structural validation only; staleness against
/// the current configuration is [`check_lock_current`].
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
    let pdf = raw.pdf.as_ref().map(|raw_pdf| LockPdf {
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

/// Collect the participating files of a path package: `lexicon.toml` and
/// regular files under `entries/`, rejecting symlinks, special files, and
/// non-UTF-8 paths (§11.5, §25.1).
pub fn collect_package_files(root: &Utf8Path) -> Result<Vec<(String, Vec<u8>)>, Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    let mut files: Vec<(String, Vec<u8>)> = Vec::new();
    let manifest = root.join("lexicon.toml");
    match std::fs::symlink_metadata(&manifest) {
        Ok(metadata) if metadata.is_file() && !metadata.file_type().is_symlink() => {
            match std::fs::read(&manifest) {
                Ok(bytes) => files.push(("lexicon.toml".to_owned(), bytes)),
                Err(io_error) => diagnostics.push(Diagnostic::new(
                    code!("LLR3001"),
                    format!("{manifest}: {io_error}"),
                )),
            }
        }
        Ok(_) => diagnostics.push(Diagnostic::new(
            code!("LLS8001"),
            format!("{manifest}: must be a regular nonsymlink file"),
        )),
        Err(io_error) => diagnostics.push(Diagnostic::new(
            code!("LLR3001"),
            format!("{manifest}: {io_error}"),
        )),
    }
    let entries = root.join("entries");
    if entries.exists() {
        for entry in walkdir::WalkDir::new(entries.as_std_path())
            .follow_links(false)
            .sort_by_file_name()
        {
            let entry = match entry {
                Ok(entry) => entry,
                Err(walk_error) => {
                    diagnostics.push(Diagnostic::new(
                        code!("LLR3001"),
                        format!("{entries}: {walk_error}"),
                    ));
                    continue;
                }
            };
            let file_type = entry.file_type();
            if file_type.is_symlink() {
                diagnostics.push(Diagnostic::new(
                    code!("LLS8001"),
                    format!("{}: symlinks are rejected", entry.path().display()),
                ));
                continue;
            }
            if file_type.is_dir() {
                continue;
            }
            if !file_type.is_file() {
                diagnostics.push(Diagnostic::new(
                    code!("LLS8001"),
                    format!("{}: special files are rejected", entry.path().display()),
                ));
                continue;
            }
            let Ok(path) = Utf8PathBuf::from_path_buf(entry.path().to_path_buf()) else {
                diagnostics.push(Diagnostic::new(
                    code!("LLS8001"),
                    format!("{}: non-UTF-8 path", entry.path().display()),
                ));
                continue;
            };
            let relative = path
                .strip_prefix(root)
                .map(|p| p.to_string())
                .unwrap_or_else(|_| path.to_string());
            match std::fs::read(&path) {
                Ok(bytes) => files.push((relative, bytes)),
                Err(io_error) => diagnostics.push(Diagnostic::new(
                    code!("LLR3001"),
                    format!("{path}: {io_error}"),
                )),
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
    let semantics_hex = crate::compiler_semantics_id();

    // Builtins: always core, plus every configured builtin source.
    let mut builtin_ids: Vec<String> = vec!["lexlean.core".to_owned()];
    for source in &project.config.lexicon_sources {
        if let LexiconSource::Builtin { package } = source {
            if package != "lexlean.core" {
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
            diagnostics.push(Diagnostic::new(
                code!("LLR3001"),
                format!("`{id}` is not a builtin package"),
            ));
            continue;
        };
        match crate::lexicon::load_builtin_package(row) {
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
        let _ = semantics_hex;
    }

    for source in &project.config.lexicon_sources {
        match source {
            LexiconSource::Builtin { .. } => {}
            LexiconSource::Path { package: id, path } => {
                let root = project.root.join(path);
                match collect_package_files(&root) {
                    Ok(files) => match load_package(path, &files, None) {
                        Ok(package) => {
                            if package.id != *id {
                                diagnostics.push(Diagnostic::new(
                                    code!("LLR3001"),
                                    format!(
                                        "`{path}` contains `{}`, not the configured `{id}`",
                                        package.id
                                    ),
                                ));
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
                match resolve_git_package(project, id, url, revision, subdirectory, allow_network) {
                    Ok((package, cache_relative)) => {
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
                        let _ = cache_relative;
                    }
                    Err(mut git_diagnostics) => diagnostics.append(&mut git_diagnostics),
                }
            }
        }
    }

    if diagnostics.is_empty() {
        Ok(ResolvedPackages { packages, rows })
    } else {
        Err(diagnostics)
    }
}

/// Resolve one Git package from the cache, acquiring it over HTTPS only
/// when `allow_network` (§11.4, §25.3).
fn resolve_git_package(
    project: &Project,
    id: &str,
    url: &str,
    revision: &str,
    subdirectory: &str,
    allow_network: bool,
) -> Result<(LexiconPackage, String), Vec<Diagnostic>> {
    let cache_base = project
        .root
        .join(&project.config.build_root)
        .join("cache")
        .join("git")
        .join(revision);
    // The cache key includes the tree digest; scan existing candidates and
    // revalidate before use.
    if cache_base.exists() {
        for entry in std::fs::read_dir(cache_base.as_std_path())
            .into_iter()
            .flatten()
            .flatten()
        {
            let Ok(candidate) = Utf8PathBuf::from_path_buf(entry.path()) else {
                continue;
            };
            if let Ok(files) = collect_package_files(&candidate) {
                if let Ok(package) = load_package(candidate.as_str(), &files, None) {
                    if package.id == id
                        && candidate.file_name() == Some(package.tree_sha256.to_hex().as_str())
                    {
                        let relative = format!(
                            "{}/cache/git/{revision}/{}",
                            project.config.build_root,
                            package.tree_sha256.to_hex()
                        );
                        return Ok((package, relative));
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
    acquire_git_package(project, id, url, revision, subdirectory, &cache_base)
}

fn git_failure(step: &str, detail: impl std::fmt::Display) -> Vec<Diagnostic> {
    vec![Diagnostic::new(
        code!("LLR3001"),
        format!("git acquisition failed at {step}: {detail}"),
    )]
}

fn acquire_git_package(
    project: &Project,
    id: &str,
    url: &str,
    revision: &str,
    subdirectory: &str,
    cache_base: &Utf8Path,
) -> Result<(LexiconPackage, String), Vec<Diagnostic>> {
    let staging = tempfile::tempdir_in(
        project
            .root
            .join(&project.config.build_root)
            .as_std_path()
            .parent()
            .unwrap_or_else(|| project.root.as_std_path()),
    );
    let staging = match staging {
        Ok(dir) => dir,
        Err(io_error) => {
            // The build root may not exist yet; fall back to it after
            // creating it.
            let base = project.root.join(&project.config.build_root);
            if std::fs::create_dir_all(base.as_std_path()).is_err() {
                return Err(git_failure("staging", io_error));
            }
            tempfile::tempdir_in(base.as_std_path())
                .map_err(|nested| git_failure("staging", nested))?
        }
    };
    let checkout = staging.path().join("checkout");
    std::fs::create_dir_all(&checkout).map_err(|io_error| git_failure("staging", io_error))?;

    // Direct executable and argument-vector invocation, no shell (§25.2),
    // prompts disabled (§25.3).
    let run_git = |arguments: &[&str]| -> Result<(), Vec<Diagnostic>> {
        let output = std::process::Command::new("git")
            .args(arguments)
            .current_dir(&checkout)
            .env("GIT_TERMINAL_PROMPT", "0")
            .env("NO_COLOR", "1")
            .env("LANG", "C.UTF-8")
            .env("LC_ALL", "C.UTF-8")
            .output()
            .map_err(|io_error| git_failure("spawn", io_error))?;
        if output.status.success() {
            Ok(())
        } else {
            Err(git_failure(
                arguments.first().copied().unwrap_or("git"),
                String::from_utf8_lossy(&output.stderr),
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

    let package_root = Utf8PathBuf::from_path_buf(checkout.join(subdirectory))
        .map_err(|bad| git_failure("subdirectory", bad.display()))?;
    // Reject submodules, LFS indirection, and nested repositories (§11.4).
    if checkout.join(".gitmodules").exists() || package_root.join(".gitmodules").exists() {
        return Err(vec![Diagnostic::new(
            code!("LLR3001"),
            format!("git package `{id}`: submodules are rejected"),
        )]);
    }
    for attributes in [
        checkout.join(".gitattributes"),
        package_root.join(".gitattributes").into_std_path_buf(),
    ] {
        if let Ok(text) = std::fs::read_to_string(&attributes) {
            if text.contains("filter=lfs") {
                return Err(vec![Diagnostic::new(
                    code!("LLR3001"),
                    format!("git package `{id}`: LFS indirection is rejected"),
                )]);
            }
        }
    }
    if package_root.join(".git").exists() {
        return Err(vec![Diagnostic::new(
            code!("LLR3001"),
            format!("git package `{id}`: nested repositories are rejected"),
        )]);
    }

    let files = collect_package_files(&package_root)?;
    let package = load_package(&format!("git:{id}"), &files, None)?;
    if package.id != id {
        return Err(vec![Diagnostic::new(
            code!("LLR3001"),
            format!(
                "git source contains `{}`, not the configured `{id}`",
                package.id
            ),
        )]);
    }
    let cache_dir = cache_base.join(package.tree_sha256.to_hex());
    std::fs::create_dir_all(cache_dir.as_std_path())
        .map_err(|io_error| git_failure("cache", io_error))?;
    for (relative, bytes) in &files {
        let destination = cache_dir.join(relative);
        if let Some(parent) = destination.parent() {
            std::fs::create_dir_all(parent.as_std_path())
                .map_err(|io_error| git_failure("cache", io_error))?;
        }
        std::fs::write(destination.as_std_path(), bytes)
            .map_err(|io_error| git_failure("cache", io_error))?;
    }
    let relative = format!(
        "{}/cache/git/{revision}/{}",
        project.config.build_root,
        package.tree_sha256.to_hex()
    );
    Ok((package, relative))
}

/// Compute the workspace pin rows (§10.4): `lean-toolchain`, exactly one
/// Lake configuration, and `lake-manifest.json` when present.
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
    match project.confined_file(&toolchain_relative) {
        Ok(absolute) => match std::fs::read(absolute.as_std_path()) {
            Ok(bytes) => rows.push((toolchain_relative.clone(), Sha256Digest::of(&bytes))),
            Err(io_error) => diagnostics.push(Diagnostic::new(
                code!("LLC0101"),
                format!("{toolchain_relative}: {io_error}"),
            )),
        },
        Err(diagnostic) => diagnostics.push(diagnostic),
    }

    let lakefile_toml = workspace_relative("lakefile.toml");
    let lakefile_lean = workspace_relative("lakefile.lean");
    let has_toml = project.absolute(&lakefile_toml).is_file();
    let has_lean = project.absolute(&lakefile_lean).is_file();
    match (has_toml, has_lean) {
        (true, true) => diagnostics.push(Diagnostic::new(
            code!("LLC0101"),
            "the Lake workspace must contain exactly one Lake configuration; both lakefile.toml and lakefile.lean exist",
        )),
        (false, false) => diagnostics.push(Diagnostic::new(
            code!("LLC0101"),
            "the Lake workspace has no lakefile.toml or lakefile.lean",
        )),
        (true, false) => match std::fs::read(project.absolute(&lakefile_toml).as_std_path()) {
            Ok(bytes) => rows.push((lakefile_toml, Sha256Digest::of(&bytes))),
            Err(io_error) => diagnostics.push(Diagnostic::new(
                code!("LLC0101"),
                format!("{lakefile_toml}: {io_error}"),
            )),
        },
        (false, true) => match std::fs::read(project.absolute(&lakefile_lean).as_std_path()) {
            Ok(bytes) => rows.push((lakefile_lean, Sha256Digest::of(&bytes))),
            Err(io_error) => diagnostics.push(Diagnostic::new(
                code!("LLC0101"),
                format!("{lakefile_lean}: {io_error}"),
            )),
        },
    }

    let manifest = workspace_relative("lake-manifest.json");
    if project.absolute(&manifest).is_file() {
        match std::fs::read(project.absolute(&manifest).as_std_path()) {
            Ok(bytes) => rows.push((manifest, Sha256Digest::of(&bytes))),
            Err(io_error) => diagnostics.push(Diagnostic::new(
                code!("LLC0101"),
                format!("{manifest}: {io_error}"),
            )),
        }
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
                _ => diagnostics.push(Diagnostic::new(
                    code!("LLR3001"),
                    format!(
                        "{}: transitive import `{import}` is not part of the configured closure",
                        package.id
                    ),
                )),
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
            program_sha256: provider.program_sha256,
            version_stdout_sha256: provider.version_stdout_sha256,
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

/// Read the committed lock and require it to be current: canonical bytes,
/// matching compiler semantics, matching project configuration, and
/// matching package digests (§11, CF-10).
pub fn read_current_lock(
    project: &Project,
) -> Result<(Lock, Vec<LexiconPackage>), Vec<Diagnostic>> {
    let lock_path = project.absolute(&project.config.lockfile);
    let bytes = std::fs::read(lock_path.as_std_path()).map_err(|io_error| {
        vec![lock_error(format!(
            "{}: {io_error}; run `lexlean lock`",
            project.config.lockfile
        ))]
    })?;
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
