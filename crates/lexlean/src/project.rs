//! Project discovery, filesystem confinement, and module selection
//! (SPEC.md §23.2, §23.3, §25.1).

use std::collections::{BTreeMap, BTreeSet};

use camino::{Utf8Path, Utf8PathBuf};

use crate::code;
use crate::config::{is_module_segment, parse_project, ProjectConfig};
use crate::diagnostic::Diagnostic;
use crate::error::LexLeanError;

/// A loaded project: canonicalized root plus validated configuration.
#[derive(Debug)]
pub struct Project {
    /// The canonicalized project root.
    pub root: Utf8PathBuf,
    /// The configuration file name relative to the root.
    pub config_name: String,
    /// The validated configuration.
    pub config: ProjectConfig,
    /// The raw configuration bytes as read.
    pub config_bytes: Vec<u8>,
}

/// The selection modes (SPEC.md §24.2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Selection {
    /// Configured entrypoints and their transitive imports.
    Entrypoints,
    /// Every `.lex.tex` beneath every source root.
    All,
    /// Explicit input files and their transitive imports. Never empty.
    Files(BTreeSet<Utf8PathBuf>),
}

fn security(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLS8001"), message)
}

fn utf8_path(path: &std::path::Path) -> Result<Utf8PathBuf, Diagnostic> {
    Utf8PathBuf::from_path_buf(path.to_path_buf())
        .map_err(|bad| security(format!("non-UTF-8 path: {}", bad.display())))
}

/// Search the working directory and its parents for the first regular
/// `lexlean.toml` (§23.2). Symlinked candidates are rejected; the search
/// stops at the filesystem root.
pub fn discover(start: &Utf8Path) -> Result<Utf8PathBuf, LexLeanError> {
    let mut current = Some(start.to_path_buf());
    while let Some(directory) = current {
        let candidate = directory.join("lexlean.toml");
        if let Ok(metadata) = std::fs::symlink_metadata(&candidate) {
            if metadata.file_type().is_symlink() {
                return Err(LexLeanError::from_diagnostic(security(format!(
                    "{candidate}: a symlinked lexlean.toml is rejected"
                ))));
            }
            if metadata.is_file() {
                return Ok(candidate);
            }
        }
        current = directory.parent().map(Utf8Path::to_path_buf);
    }
    Err(LexLeanError::from_diagnostic(Diagnostic::new(
        code!("LLC0101"),
        format!("no lexlean.toml found from {start} upward"),
    )))
}

impl Project {
    /// Load a project from its configuration file path.
    pub fn load(config_path: &Utf8Path) -> Result<Self, LexLeanError> {
        let metadata = std::fs::symlink_metadata(config_path).map_err(|io_error| {
            LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLC0101"),
                format!("{config_path}: {io_error}"),
            ))
        })?;
        if metadata.file_type().is_symlink() || !metadata.is_file() {
            return Err(LexLeanError::from_diagnostic(security(format!(
                "{config_path}: the project configuration must be a regular file"
            ))));
        }
        let parent = config_path
            .parent()
            .ok_or_else(|| {
                LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLC0101"),
                    format!("{config_path} has no parent directory"),
                ))
            })?
            .to_path_buf();
        let parent = if parent.as_str().is_empty() {
            Utf8PathBuf::from(".")
        } else {
            parent
        };
        // Canonicalize the project root exactly once (§25.1).
        let root_std = std::fs::canonicalize(parent.as_std_path()).map_err(|io_error| {
            LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLC0101"),
                format!("{parent}: {io_error}"),
            ))
        })?;
        let root = utf8_path(&root_std).map_err(LexLeanError::from_diagnostic)?;
        let config_name = config_path.file_name().unwrap_or("lexlean.toml").to_owned();
        let config_bytes = std::fs::read(config_path).map_err(|io_error| {
            LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLC0101"),
                format!("{config_path}: {io_error}"),
            ))
        })?;
        let config =
            parse_project(&config_name, &config_bytes).map_err(LexLeanError::from_diagnostics)?;

        let project = Self {
            root,
            config_name,
            config,
            config_bytes,
        };
        // The build root must resolve within the project and must not be a
        // symlink (§10.1).
        let build_root = project.root.join(&project.config.build_root);
        if let Ok(metadata) = std::fs::symlink_metadata(&build_root) {
            if metadata.file_type().is_symlink() {
                return Err(LexLeanError::from_diagnostic(security(format!(
                    "{}: the build root must not be a symlink",
                    project.config.build_root
                ))));
            }
        }
        Ok(project)
    }

    /// An absolute path under the project root for a project-relative path.
    #[must_use]
    pub fn absolute(&self, relative: &str) -> Utf8PathBuf {
        self.root.join(relative)
    }

    /// Verify a project-relative path denotes a regular file with no
    /// symlink component under the project root, and return its absolute
    /// path (§25.1).
    pub fn confined_file(&self, relative: &str) -> Result<Utf8PathBuf, Diagnostic> {
        if !crate::config::is_project_relative(relative) {
            return Err(security(format!("`{relative}` escapes the project root")));
        }
        let mut current = self.root.clone();
        for segment in relative.split('/') {
            current.push(segment);
            let metadata = std::fs::symlink_metadata(&current)
                .map_err(|io_error| security(format!("{current}: {io_error}")))?;
            if metadata.file_type().is_symlink() {
                return Err(security(format!("{current}: symlinks are rejected")));
            }
        }
        let metadata = std::fs::symlink_metadata(&current)
            .map_err(|io_error| security(format!("{current}: {io_error}")))?;
        if !metadata.is_file() {
            return Err(security(format!("{current}: expected a regular file")));
        }
        Ok(current)
    }

    /// The module name for a source path relative to one of the configured
    /// source roots: the path minus `.lex.tex`, `/` becoming `.`, every
    /// segment a Lean-name segment.
    pub fn module_name_for(&self, project_relative: &str) -> Result<String, Diagnostic> {
        let Some((_, inside)) = self.config.source_roots.iter().find_map(|root| {
            project_relative
                .strip_prefix(root.as_str())
                .and_then(|rest| rest.strip_prefix('/'))
                .map(|inside| (root, inside))
        }) else {
            return Err(Diagnostic::new(
                code!("LLC0002"),
                format!("`{project_relative}` is not beneath a configured source root"),
            ));
        };
        let Some(stem) = inside.strip_suffix(".lex.tex") else {
            return Err(Diagnostic::new(
                code!("LLC0002"),
                format!("`{project_relative}` is not a .lex.tex module"),
            ));
        };
        let name = stem.replace('/', ".");
        if !name.split('.').all(is_module_segment) {
            return Err(Diagnostic::new(
                code!("LLC0101"),
                format!("`{project_relative}` is not a valid module path"),
            ));
        }
        Ok(name)
    }

    /// Every `.lex.tex` module beneath every source root, as
    /// `module name -> project-relative path`. Symlinks and special files
    /// are rejected; duplicate logical modules and case-fold collisions are
    /// errors (§23.3, §25.1).
    pub fn all_modules(&self) -> Result<BTreeMap<String, String>, Vec<Diagnostic>> {
        let mut diagnostics = Vec::new();
        let mut modules: BTreeMap<String, String> = BTreeMap::new();
        let mut identities: Vec<(same_file::Handle, String)> = Vec::new();
        for root in &self.config.source_roots {
            let absolute_root = self.root.join(root);
            if !absolute_root.exists() {
                continue;
            }
            for entry in walkdir::WalkDir::new(absolute_root.as_std_path())
                .follow_links(false)
                .sort_by_file_name()
            {
                let entry = match entry {
                    Ok(entry) => entry,
                    Err(walk_error) => {
                        diagnostics.push(security(format!("{root}: {walk_error}")));
                        continue;
                    }
                };
                let file_type = entry.file_type();
                if file_type.is_symlink() {
                    diagnostics.push(security(format!(
                        "{}: symlinks are rejected in source roots",
                        entry.path().display()
                    )));
                    continue;
                }
                if !file_type.is_file() {
                    continue;
                }
                let path = match utf8_path(entry.path()) {
                    Ok(path) => path,
                    Err(diagnostic) => {
                        diagnostics.push(diagnostic);
                        continue;
                    }
                };
                if !path.as_str().ends_with(".lex.tex") {
                    continue;
                }
                let relative = path
                    .strip_prefix(&self.root)
                    .map(Utf8Path::to_string)
                    .unwrap_or_else(|_| path.to_string());
                match same_file::Handle::from_path(path.as_std_path()) {
                    Ok(handle) => {
                        if let Some((_, existing)) = identities
                            .iter()
                            .find(|(candidate, _)| *candidate == handle)
                        {
                            diagnostics.push(Diagnostic::new(
                                code!("LLC0104"),
                                format!("`{relative}` and `{existing}` are the same file"),
                            ));
                            continue;
                        }
                        identities.push((handle, relative.clone()));
                    }
                    Err(io_error) => {
                        diagnostics.push(security(format!("{relative}: {io_error}")));
                        continue;
                    }
                }
                match self.module_name_for(&relative) {
                    Ok(module) => {
                        if let Some(existing) = modules.get(&module) {
                            diagnostics.push(Diagnostic::new(
                                code!("LLC0104"),
                                format!(
                                    "`{relative}` and `{existing}` declare the same module `{module}`"
                                ),
                            ));
                        } else {
                            modules.insert(module, relative);
                        }
                    }
                    Err(diagnostic) => diagnostics.push(diagnostic),
                }
            }
        }
        // Case-fold collisions (§23.3).
        let mut folded: BTreeMap<String, &String> = BTreeMap::new();
        for module in modules.keys() {
            let key = module.to_lowercase();
            if let Some(existing) = folded.get(&key) {
                diagnostics.push(Diagnostic::new(
                    code!("LLC0104"),
                    format!("modules `{existing}` and `{module}` collide under case folding"),
                ));
            } else {
                folded.insert(key, module);
            }
        }
        if diagnostics.is_empty() {
            Ok(modules)
        } else {
            Err(diagnostics)
        }
    }

    /// Resolve a selection to `module name -> project-relative path`
    /// (§23.3). Import closure joins later, after headers parse.
    pub fn resolve_selection(
        &self,
        selection: &Selection,
    ) -> Result<BTreeMap<String, String>, Vec<Diagnostic>> {
        let all = self.all_modules()?;
        match selection {
            Selection::All => Ok(all),
            Selection::Entrypoints => {
                let mut selected = BTreeMap::new();
                let mut diagnostics = Vec::new();
                for entrypoint in &self.config.entrypoints {
                    match self.module_name_for(entrypoint) {
                        Ok(module) => {
                            if all.get(&module) == Some(entrypoint) {
                                selected.insert(module, entrypoint.clone());
                            } else {
                                diagnostics.push(Diagnostic::new(
                                    code!("LLC0101"),
                                    format!("entrypoint `{entrypoint}` does not exist"),
                                ));
                            }
                        }
                        Err(diagnostic) => diagnostics.push(diagnostic),
                    }
                }
                if diagnostics.is_empty() {
                    Ok(selected)
                } else {
                    Err(diagnostics)
                }
            }
            Selection::Files(files) => {
                if files.is_empty() {
                    return Err(vec![Diagnostic::new(
                        code!("LLC0002"),
                        "an explicit file selection cannot be empty",
                    )]);
                }
                let mut selected = BTreeMap::new();
                let mut diagnostics = Vec::new();
                for input in files {
                    // Inputs are project-relative or absolute paths that
                    // resolve beneath a configured source root.
                    let relative = if input.is_absolute() {
                        match std::fs::canonicalize(input.as_std_path())
                            .ok()
                            .and_then(|absolute| utf8_path(&absolute).ok())
                            .and_then(|absolute| {
                                absolute
                                    .strip_prefix(&self.root)
                                    .map(Utf8Path::to_string)
                                    .ok()
                            }) {
                            Some(relative) => relative,
                            None => {
                                diagnostics.push(Diagnostic::new(
                                    code!("LLC0002"),
                                    format!("`{input}` does not resolve inside the project"),
                                ));
                                continue;
                            }
                        }
                    } else {
                        input.to_string()
                    };
                    match self.module_name_for(&relative) {
                        Ok(module) => {
                            if all.get(&module) == Some(&relative) {
                                if selected.insert(module.clone(), relative.clone()).is_some() {
                                    diagnostics.push(Diagnostic::new(
                                        code!("LLC0104"),
                                        format!("module `{module}` is selected twice"),
                                    ));
                                }
                            } else {
                                diagnostics.push(Diagnostic::new(
                                    code!("LLC0002"),
                                    format!("`{relative}` does not exist beneath a source root"),
                                ));
                            }
                        }
                        Err(diagnostic) => diagnostics.push(diagnostic),
                    }
                }
                if diagnostics.is_empty() {
                    Ok(selected)
                } else {
                    Err(diagnostics)
                }
            }
        }
    }
}
