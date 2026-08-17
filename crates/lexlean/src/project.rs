//! Project discovery, filesystem confinement, and module selection
//! (SPEC.md §23.2, §23.3, §25.1).

use std::collections::{BTreeMap, BTreeSet};

use camino::{Utf8Path, Utf8PathBuf};

use crate::code;
use crate::config::{is_module_segment, parse_project, ProjectConfig};
use crate::diagnostic::Diagnostic;
use crate::error::LexLeanError;

/// Rewrite a path the host rendered with its own separator into the
/// canonical `/`-separated project-relative spelling.
///
/// §10.1 fixes a project-relative path as `/`-separated, and those exact
/// bytes are what the configuration, the lock, the manifests, the source
/// maps, and every diagnostic carry. A host whose separator is the
/// backslash renders `src\Main.lex.tex` where the project spells
/// `src/Main.lex.tex`, and nothing downstream recognizes it: module naming
/// would reject its own source root and a lock digest would differ from
/// every other host's for identical bytes (§8.3, R10).
///
/// A backslash is an ordinary character in a unix file name, so only a host
/// that actually separates with one rewrites it. The separator is a
/// parameter so the rule is decidable on every host, not only where it
/// bites.
#[must_use]
pub(crate) fn separated(rendered: &str, separator: char) -> String {
    if separator == '/' {
        rendered.to_owned()
    } else {
        rendered.replace(separator, "/")
    }
}

/// [`separated`] for this host.
#[must_use]
pub(crate) fn project_relative(rendered: &str) -> String {
    separated(rendered, std::path::MAIN_SEPARATOR)
}

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

/// A non-UTF-8 path is outside language 1.0 and an environment failure
/// (§8.3), never a security violation.
pub fn non_utf8_path(path: &std::path::Path) -> Diagnostic {
    Diagnostic::new(
        code!("LLV7008"),
        format!(
            "non-UTF-8 path in the environment: {}",
            path.to_string_lossy()
        ),
    )
}

/// Convert a host path to UTF-8 or report the §8.3 environment diagnostic.
pub fn utf8_path(path: &std::path::Path) -> Result<Utf8PathBuf, Diagnostic> {
    Utf8PathBuf::from_path_buf(path.to_path_buf()).map_err(|bad| non_utf8_path(&bad))
}

/// Search the working directory and its parents for the first regular
/// `lexlean.toml` (§23.2). Symlinked candidates are rejected; the search
/// stops at the filesystem root.
pub fn discover(start: &Utf8Path) -> Result<Utf8PathBuf, LexLeanError> {
    let mut current = Some(start.to_path_buf());
    let mut depth = 0usize;
    while let Some(directory) = current {
        let candidate = directory.join("lexlean.toml");
        if let Ok(metadata) = std::fs::symlink_metadata(&candidate) {
            if metadata.file_type().is_symlink() {
                // Named relative to the working directory, never absolutely
                // (§20.6, §23.7).
                let shown = format!("{}lexlean.toml", "../".repeat(depth));
                return Err(LexLeanError::from_diagnostic(security(format!(
                    "`{shown}`: a symlinked lexlean.toml candidate is rejected"
                ))));
            }
            if metadata.is_file() {
                return Ok(candidate);
            }
        }
        current = directory.parent().map(Utf8Path::to_path_buf);
        depth = depth.saturating_add(1);
    }
    Err(LexLeanError::from_diagnostic(Diagnostic::new(
        code!("LLC0101"),
        "no lexlean.toml found in the working directory or any parent; pass --project or run inside a project",
    )))
}

/// What a confined path must denote once every component is checked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Expect {
    /// A regular file.
    File,
    /// A directory.
    Directory,
    /// Anything, or nothing yet: only the symlink walk applies, and a
    /// missing suffix of components is tolerated (paths about to be
    /// created, such as the build root or the lock file).
    Creatable,
}

impl Project {
    /// Load a project from its configuration file path.
    pub fn load(config_path: &Utf8Path) -> Result<Self, LexLeanError> {
        // Messages name the configuration as the user gave it when that is
        // relative, and by file name otherwise (§20.6: no absolute paths).
        let shown: String = if config_path.is_absolute() {
            config_path.file_name().unwrap_or("lexlean.toml").to_owned()
        } else {
            config_path.to_string()
        };
        let metadata = std::fs::symlink_metadata(config_path).map_err(|io_error| {
            LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLC0101"),
                format!("{shown}: {io_error}"),
            ))
        })?;
        if metadata.file_type().is_symlink() || !metadata.is_file() {
            return Err(LexLeanError::from_diagnostic(security(format!(
                "{shown}: the project configuration must be a regular file"
            ))));
        }
        let parent = config_path
            .parent()
            .ok_or_else(|| {
                LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLC0101"),
                    format!("{shown} has no parent directory"),
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
                format!("the directory of {shown}: {io_error}"),
            ))
        })?;
        let root = utf8_path(&root_std).map_err(LexLeanError::from_diagnostic)?;
        let config_name = config_path.file_name().unwrap_or("lexlean.toml").to_owned();
        let config_bytes = std::fs::read(config_path).map_err(|io_error| {
            LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLC0101"),
                format!("{shown}: {io_error}"),
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
        // The build root must resolve within the project and no component
        // of it may be a symlink (§10.1, §25.1); the same holds for the
        // lock file path and the Lake workspace directory.
        let build_root = project.config.build_root.clone();
        project
            .confined(&build_root, Expect::Creatable)
            .map_err(LexLeanError::from_diagnostic)?;
        let lockfile = project.config.lockfile.clone();
        project
            .confined(&lockfile, Expect::Creatable)
            .map_err(LexLeanError::from_diagnostic)?;
        if project.config.lean_workspace != "." {
            let workspace = project.config.lean_workspace.clone();
            project
                .confined(&workspace, Expect::Creatable)
                .map_err(LexLeanError::from_diagnostic)?;
        }
        Ok(project)
    }

    /// An absolute path under the project root for a project-relative path.
    #[must_use]
    pub fn absolute(&self, relative: &str) -> Utf8PathBuf {
        self.root.join(relative)
    }

    /// The project-relative rendering of a path for diagnostics (§23.7):
    /// the root prefix removed when the path lies inside the project,
    /// otherwise the path unchanged.
    #[must_use]
    pub fn display(&self, path: &Utf8Path) -> String {
        match path.strip_prefix(&self.root) {
            Ok(inside) if inside.as_str().is_empty() => ".".to_owned(),
            Ok(inside) => project_relative(inside.as_str()),
            Err(_) => path.to_string(),
        }
    }

    /// The project-relative rendering of a host path.
    #[must_use]
    pub fn display_std(&self, path: &std::path::Path) -> String {
        match Utf8Path::from_path(path) {
            Some(utf8) => self.display(utf8),
            None => path.to_string_lossy().into_owned(),
        }
    }

    /// Walk every component of a project-relative path with
    /// `symlink_metadata`, rejecting symlinks and (for the last component)
    /// the wrong kind. Diagnostics name project-relative paths.
    fn confined(&self, relative: &str, expect: Expect) -> Result<Utf8PathBuf, Diagnostic> {
        if !crate::config::is_project_relative(relative) {
            return Err(security(format!("`{relative}` escapes the project root")));
        }
        let mut current = self.root.clone();
        let mut walked = String::new();
        for segment in relative.split('/') {
            current.push(segment);
            if !walked.is_empty() {
                walked.push('/');
            }
            walked.push_str(segment);
            match std::fs::symlink_metadata(&current) {
                Ok(metadata) => {
                    if metadata.file_type().is_symlink() {
                        return Err(security(format!(
                            "`{walked}`: symlinks are rejected in confined paths"
                        )));
                    }
                }
                Err(io_error) if io_error.kind() == std::io::ErrorKind::NotFound => {
                    return match expect {
                        // Nothing below a missing component can be a
                        // symlink yet; the full path is what the caller
                        // is about to create.
                        Expect::Creatable => Ok(self.root.join(relative)),
                        Expect::File | Expect::Directory => {
                            Err(security(format!("`{walked}`: {io_error}")))
                        }
                    };
                }
                Err(io_error) => return Err(security(format!("`{walked}`: {io_error}"))),
            }
        }
        let metadata = std::fs::symlink_metadata(&current)
            .map_err(|io_error| security(format!("`{relative}`: {io_error}")))?;
        match expect {
            Expect::File if !metadata.is_file() => {
                Err(security(format!("`{relative}`: expected a regular file")))
            }
            Expect::Directory if !metadata.is_dir() => {
                Err(security(format!("`{relative}`: expected a directory")))
            }
            _ => Ok(current),
        }
    }

    /// Verify a project-relative path denotes a regular file with no
    /// symlink component under the project root, and return its absolute
    /// path (§25.1).
    pub fn confined_file(&self, relative: &str) -> Result<Utf8PathBuf, Diagnostic> {
        self.confined(relative, Expect::File)
    }

    /// Like [`Self::confined_file`], but a path that simply does not exist
    /// is the caller's own failure — a missing lock is a lock error, a
    /// missing workspace pin an environment one — rather than a
    /// confinement violation (§23.6: exit 4 is for a security-policy or
    /// resource-limit violation, which a missing file is not).
    pub fn confined_file_or_missing(
        &self,
        relative: &str,
        missing: impl FnOnce() -> Diagnostic,
    ) -> Result<Utf8PathBuf, Diagnostic> {
        if crate::config::is_project_relative(relative) {
            let candidate = self.root.join(relative);
            if std::fs::symlink_metadata(candidate.as_std_path())
                .is_err_and(|io_error| io_error.kind() == std::io::ErrorKind::NotFound)
            {
                return Err(missing());
            }
        }
        self.confined_file(relative)
    }

    /// Verify a project-relative path denotes a directory with no symlink
    /// component under the project root, and return its absolute path
    /// (§25.1).
    pub fn confined_dir(&self, relative: &str) -> Result<Utf8PathBuf, Diagnostic> {
        self.confined(relative, Expect::Directory)
    }

    /// Verify that every existing component of a project-relative path is
    /// a nonsymlink; a missing suffix is tolerated because the path is
    /// about to be created (the build root, the lock file).
    pub fn confined_creatable(&self, relative: &str) -> Result<Utf8PathBuf, Diagnostic> {
        self.confined(relative, Expect::Creatable)
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
            let absolute_root = match self.confined(root, Expect::Creatable) {
                Ok(absolute) => absolute,
                Err(diagnostic) => {
                    diagnostics.push(diagnostic);
                    continue;
                }
            };
            // A configured source root that does not exist is a broken
            // configuration, not an empty one (§10.1: source roots are
            // project-relative directories).
            match std::fs::symlink_metadata(absolute_root.as_std_path()) {
                Ok(metadata) if metadata.is_dir() => {}
                Ok(_) => {
                    diagnostics.push(Diagnostic::new(
                        code!("LLC0101"),
                        format!("source root `{root}` is not a directory"),
                    ));
                    continue;
                }
                Err(io_error) => {
                    diagnostics.push(Diagnostic::new(
                        code!("LLC0101"),
                        format!("source root `{root}`: {io_error}"),
                    ));
                    continue;
                }
            }
            for entry in walkdir::WalkDir::new(absolute_root.as_std_path())
                .follow_links(false)
                .sort_by_file_name()
            {
                let entry = match entry {
                    Ok(entry) => entry,
                    Err(walk_error) => {
                        diagnostics.push(security(format!("`{root}`: {walk_error}")));
                        continue;
                    }
                };
                let file_type = entry.file_type();
                if file_type.is_symlink() {
                    diagnostics.push(security(format!(
                        "`{}`: symlinks are rejected in source roots",
                        self.display_std(entry.path())
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
                let relative = self.display(&path);
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
                        diagnostics.push(security(format!("`{relative}`: {io_error}")));
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

    /// Normalize one explicit input to a project-relative path: absolute
    /// inputs canonicalize under the root; relative inputs drop any number
    /// of leading `./` prefixes and are then required to be
    /// project-relative in the §10.1 sense.
    fn input_relative(&self, input: &Utf8Path) -> Result<String, Diagnostic> {
        if input.is_absolute() {
            let canonical = std::fs::canonicalize(input.as_std_path())
                .map_err(|io_error| {
                    Diagnostic::new(code!("LLC0002"), format!("`{input}`: {io_error}"))
                })
                .and_then(|absolute| utf8_path(&absolute))?;
            return canonical
                .strip_prefix(&self.root)
                .map(|inside| project_relative(inside.as_str()))
                .map_err(|_| {
                    Diagnostic::new(
                        code!("LLC0002"),
                        format!("`{input}` does not resolve inside the project"),
                    )
                });
        }
        let mut text = input.as_str();
        while let Some(rest) = text.strip_prefix("./") {
            text = rest;
        }
        if !crate::config::is_project_relative(text) {
            return Err(Diagnostic::new(
                code!("LLC0002"),
                format!("`{input}` is not a project-relative or absolute input path"),
            ));
        }
        Ok(text.to_owned())
    }

    /// Resolve a selection to `module name -> project-relative path`
    /// (§23.3). Import closure joins later, after headers parse.
    pub fn resolve_selection(
        &self,
        selection: &Selection,
    ) -> Result<BTreeMap<String, String>, Vec<Diagnostic>> {
        let all = self.all_modules()?;
        match selection {
            // §23.3: `--all` is every module beneath every source root; a
            // project with none selects nothing, and an empty selection is
            // a selection error (§23.6 exit 2), not a vacuous success.
            Selection::All if all.is_empty() => Err(vec![Diagnostic::new(
                code!("LLC0002"),
                "`--all` selects no module: no source root holds a `.lex.tex` file".to_owned(),
            )]),
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
                let mut seen_relative: BTreeMap<String, Utf8PathBuf> = BTreeMap::new();
                for input in files {
                    let relative = match self.input_relative(input) {
                        Ok(relative) => relative,
                        Err(diagnostic) => {
                            diagnostics.push(diagnostic);
                            continue;
                        }
                    };
                    // Two spellings of one input are a duplicate selection
                    // (§23.3), never silently collapsed.
                    if let Some(earlier) = seen_relative.get(&relative) {
                        diagnostics.push(Diagnostic::new(
                            code!("LLC0002"),
                            format!(
                                "`{input}` and `{earlier}` select the same module file `{relative}` twice"
                            ),
                        ));
                        continue;
                    }
                    seen_relative.insert(relative.clone(), input.clone());
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

#[cfg(test)]
mod tests {
    use super::{project_relative, separated};

    /// §10.1, §8.3: a project-relative path is `/`-separated whatever the
    /// host renders, and a backslash that is not a separator is an ordinary
    /// character in a file name.
    #[test]
    fn a_project_relative_path_is_slash_separated_on_every_host() {
        assert_eq!(separated("src\\Main.lex.tex", '\\'), "src/Main.lex.tex");
        assert_eq!(
            separated("src\\deep\\Main.lex.tex", '\\'),
            "src/deep/Main.lex.tex"
        );
        assert_eq!(separated("src/Main.lex.tex", '/'), "src/Main.lex.tex");
        assert_eq!(separated("odd\\name.lex.tex", '/'), "odd\\name.lex.tex");
        assert_eq!(separated("", '\\'), "");
        // The host wrapper agrees with the rule for this host's separator.
        assert_eq!(
            project_relative("src\\Main.lex.tex"),
            separated("src\\Main.lex.tex", std::path::MAIN_SEPARATOR)
        );
    }
}
