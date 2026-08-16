//! Shared fixtures for the conformance cases: temporary project copies,
//! engine drivers, diagnostic assertions, fixture lexicon packages, and
//! the shared Lean-backed runs (the toolchain is the expensive part; the
//! assertions differ per case).

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::{Mutex, MutexGuard, OnceLock};

use camino::{Utf8Path, Utf8PathBuf};
use lexlean::error::LexLeanError;
use lexlean::{
    BuildRequest, CheckRequest, Engine, FormatRequest, LockRequest, Selection, VerifyRequest,
};

/// The repository root.
#[must_use]
pub fn repo_root() -> Utf8PathBuf {
    let manifest = Utf8PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .ancestors()
        .nth(2)
        .expect("crates/conformance is two below the root")
        .to_path_buf()
}

/// The whole specification text, read once.
pub fn spec_text() -> &'static str {
    static TEXT: OnceLock<String> = OnceLock::new();
    TEXT.get_or_init(|| {
        std::fs::read_to_string(repo_root().join("SPEC.md").as_std_path()).expect("SPEC.md")
    })
}

/// A temporary, mutable copy of a project.
pub struct P {
    #[allow(dead_code)]
    temp: tempfile::TempDir,
    /// The project root.
    pub root: Utf8PathBuf,
}

fn copy_tree(from: &Path, to: &Path, skip: &[&str]) {
    for entry in walkdir::WalkDir::new(from).into_iter().flatten() {
        let relative = entry.path().strip_prefix(from).expect("under root");
        let text = relative.to_string_lossy();
        if text.is_empty() || skip.iter().any(|prefix| text.starts_with(prefix)) {
            continue;
        }
        let destination = to.join(relative);
        if entry.file_type().is_dir() {
            std::fs::create_dir_all(&destination).expect("copy dir");
        } else if entry.file_type().is_file() {
            if let Some(parent) = destination.parent() {
                std::fs::create_dir_all(parent).expect("copy parent");
            }
            std::fs::copy(entry.path(), &destination).expect("copy file");
        }
    }
}

impl P {
    /// A fresh copy of `examples/nat-add-zero`.
    #[must_use]
    pub fn example() -> Self {
        let temp = tempfile::Builder::new()
            .prefix("lexlean-case-")
            .tempdir()
            .expect("tempdir");
        let source = repo_root().join("examples/nat-add-zero");
        copy_tree(source.as_std_path(), temp.path(), &[".lexlean", "expected"]);
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).expect("utf8 tempdir");
        Self { temp, root }
    }

    /// The engine over this copy.
    #[must_use]
    pub fn engine(&self) -> Engine {
        Engine::load(&self.root.join("lexlean.toml")).expect("project loads")
    }

    /// Read a project file.
    #[must_use]
    pub fn read(&self, relative: &str) -> String {
        std::fs::read_to_string(self.root.join(relative).as_std_path()).expect("read")
    }

    /// Overwrite a project file.
    pub fn write(&self, relative: &str, content: &str) {
        let path = self.root.join(relative);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent.as_std_path()).expect("parent");
        }
        std::fs::write(path.as_std_path(), content).expect("write");
    }

    /// Replace one occurrence, asserting it exists.
    pub fn edit(&self, relative: &str, from: &str, to: &str) {
        let text = self.read(relative);
        assert!(text.contains(from), "{relative} does not contain {from:?}");
        self.write(relative, &text.replacen(from, to, 1));
    }

    /// Regenerate the lock (after configuration or package mutations).
    pub fn relock(&self) {
        self.engine()
            .lock(LockRequest {
                check_only: false,
                allow_network: false,
            })
            .expect("relock");
    }

    /// Check the entrypoints, expecting success.
    pub fn check_ok(&self) -> lexlean::ProjectResultSet<lexlean::CheckedUnit> {
        self.engine()
            .check(CheckRequest {
                selection: Selection::Entrypoints,
            })
            .expect("check succeeds")
    }

    /// Check the entrypoints, expecting a failure.
    pub fn check_err(&self) -> LexLeanError {
        self.engine()
            .check(CheckRequest {
                selection: Selection::Entrypoints,
            })
            .err()
            .expect("check fails")
    }

    /// Check the entrypoints, expecting the given diagnostic code.
    pub fn check_fails_with(&self, code: &str) -> LexLeanError {
        let error = self.check_err();
        expect_code(&error, code);
        error
    }

    /// Build the entrypoints, expecting success.
    pub fn build_ok(&self) -> lexlean::ProjectResultSet<lexlean::BuiltUnit> {
        self.engine()
            .build(BuildRequest {
                selection: Selection::Entrypoints,
            })
            .expect("build succeeds")
    }

    /// Verify, expecting the given diagnostic code.
    pub fn verify_fails_with(&self, code: &str) -> LexLeanError {
        let error = self
            .engine()
            .verify(VerifyRequest {
                selection: Selection::Entrypoints,
            })
            .err()
            .expect("verify fails");
        expect_code(&error, code);
        error
    }

    /// Format-check, expecting success.
    pub fn fmt_check_ok(&self) {
        self.engine()
            .format(FormatRequest {
                selection: Selection::Entrypoints,
                check_only: true,
            })
            .expect("fmt --check succeeds");
    }

    /// Run the CLI in-process from this project's root.
    #[must_use]
    pub fn cli(&self, arguments: &[&str]) -> (i32, String, String) {
        cli_in(&self.root, arguments)
    }

    /// The published build directory for a build ID.
    #[must_use]
    pub fn build_dir(&self, build_id: &lexlean::artifact::content_id::Sha256Digest) -> Utf8PathBuf {
        self.root.join(".lexlean/build").join(build_id.to_hex())
    }

    /// Append a path lexicon source to the configuration (before `[limits]`).
    pub fn add_lexicon_source(&self, package: &str, path: &str) {
        self.edit(
            "lexlean.toml",
            "\n[limits]",
            &format!(
                "\n[[lexicon_source]]\npackage = \"{package}\"\nkind = \"path\"\npath = \"{path}\"\n\n[limits]"
            ),
        );
    }

    /// Write a fixture lexicon package and register it; the caller relocks.
    pub fn add_package(
        &self,
        dir: &str,
        package: &str,
        imports: &[&str],
        entries: &[(&str, &str)],
    ) {
        let import_rows = imports
            .iter()
            .map(|import| format!("\"{import}\""))
            .collect::<Vec<_>>()
            .join(", ");
        self.write(
            &format!("{dir}/lexicon.toml"),
            &format!(
                "spec = \"lexlean/lexicon/1\"\npackage = \"{package}\"\nversion = \"1.0.0\"\nlanguage = \"1.0\"\nimports = [{import_rows}]\n"
            ),
        );
        for (entry_file, content) in entries {
            self.write(&format!("{dir}/entries/{entry_file}"), content);
        }
        self.add_lexicon_source(package, dir);
    }
}

/// Run the CLI in-process from a working directory.
#[must_use]
pub fn cli_in(directory: &Utf8Path, arguments: &[&str]) -> (i32, String, String) {
    let mut argv = vec!["lexlean".to_owned()];
    argv.extend(arguments.iter().map(|s| (*s).to_owned()));
    let mut stdout = Vec::new();
    let mut stderr = Vec::new();
    let exit = lexlean::cli::run(&argv, directory, &mut stdout, &mut stderr);
    (
        exit,
        String::from_utf8_lossy(&stdout).into_owned(),
        String::from_utf8_lossy(&stderr).into_owned(),
    )
}

/// Assert an error carries the given diagnostic code.
pub fn expect_code(error: &LexLeanError, code: &str) {
    assert!(
        error
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code.as_str() == code),
        "expected {code}, found {:?} ({error})",
        error
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code.as_str())
            .collect::<Vec<_>>(),
    );
}

/// The serialization lock for tests that mutate process environment
/// variables. Shared Lean-backed fixtures also initialize under it, so an
/// environment mutation can never race toolchain resolution.
pub fn env_lock() -> MutexGuard<'static, ()> {
    static LOCK: Mutex<()> = Mutex::new(());
    LOCK.lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Run `body` with environment overrides, restoring the previous values.
/// `None` removes the variable.
pub fn with_env<T>(pairs: &[(&str, Option<&str>)], body: impl FnOnce() -> T) -> T {
    /// Restores the saved values on drop, so a panicking body (a failed
    /// assertion) cannot leave a temporary value in the process
    /// environment for every later test.
    struct Restore(Vec<(String, Option<String>)>);
    impl Drop for Restore {
        fn drop(&mut self) {
            for (key, value) in self.0.drain(..) {
                match value {
                    Some(value) => std::env::set_var(&key, value),
                    None => std::env::remove_var(&key),
                }
            }
        }
    }
    let _guard = env_lock();
    let _restore = Restore(
        pairs
            .iter()
            .map(|(key, _)| ((*key).to_owned(), std::env::var(key).ok()))
            .collect(),
    );
    for (key, value) in pairs {
        match value {
            Some(value) => std::env::set_var(key, value),
            None => std::env::remove_var(key),
        }
    }
    body()
}

/// The one shared verified run of the literal example, computed lazily.
pub struct VerifiedFixture {
    /// The project copy, kept alive for the whole test process.
    pub project: P,
    /// The verify outcome.
    pub outcome: lexlean::VerifiedProject,
    /// The parsed attestation object.
    pub attestation: serde_json::Value,
}

/// Lean-backed positive cases share this single verified run.
pub fn verified() -> &'static VerifiedFixture {
    static FIXTURE: OnceLock<VerifiedFixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let _guard = env_lock();
        let project = P::example();
        let outcome = project
            .engine()
            .verify(VerifyRequest {
                selection: Selection::Entrypoints,
            })
            .expect("the literal example verifies (EX-01); is leanprover/lean4:v4.32.1 installed?");
        let attestation: serde_json::Value = serde_json::from_slice(
            &std::fs::read(outcome.root.join("attestation.json").as_std_path())
                .expect("attestation exists"),
        )
        .expect("attestation parses");
        VerifiedFixture {
            project,
            outcome,
            attestation,
        }
    })
}

/// The shared failed run: `=` changed to a false proposition while the old
/// reflexivity proof is retained (SPEC.md §29.6 mutation 1). Conservative
/// elaboration accepts it; Lean rejects it; the diagnostic remaps.
pub fn broken_proof() -> &'static (P, LexLeanError) {
    static FIXTURE: OnceLock<(P, LexLeanError)> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let _guard = env_lock();
        let project = P::example();
        project.edit("src/Main.lex.tex", "\\(n + 0 = n\\)", "\\(n + 0 = 0\\)");
        let error = project
            .engine()
            .verify(VerifyRequest {
                selection: Selection::Entrypoints,
            })
            .err()
            .expect("the false proposition fails Lean verification");
        (project, error)
    })
}

/// The `em` fixture package: a proof constant denoting `Classical.em`, and
/// a math-channel zero so the statement avoids bare numerals.
const EM_ENTRY: &str = r#"spec = "lexlean/entry/1"
id = "em"
category = "proof-constant"
signature = "(pi ((explicit p (sort prop))) (app (const lexlean.core::lor) (local p) (app (const lexlean.core::lnot) (local p))))"
surface_arity = 1
frame = "call"

[denotation]
kind = "lean"
module = "Init"
name = "Classical.em"

[[form]]
id = "em"
channel = "math"
surface = "em"
canonical_source = true
features = []

[render]
math = "(seq (operator-name em) (paren (slot 0)))"
"#;

const Z_ENTRY: &str = r#"spec = "lexlean/entry/1"
id = "z"
category = "term-constant"
signature = "(const lexlean.std.nat::nat)"
surface_arity = 0
frame = "atom"

[denotation]
kind = "lean"
module = "Init"
name = "Nat.zero"

[[form]]
id = "z"
channel = "both"
surface = "z"
canonical_source = true
features = []

[render]
math = "(operator-name z)"
"#;

/// A project whose theorem depends on `Classical.em` under `policy`.
#[must_use]
pub fn em_project(policy: &str) -> P {
    let project = P::example();
    project.add_package(
        "lexicons/test-axioms",
        "test.axioms",
        &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
        &[("em.toml", EM_ENTRY), ("z.toml", Z_ENTRY)],
    );
    project.write(
        "src/Main.lex.tex",
        &format!(
            "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\useglossary{{test.axioms@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{excluded}}\n{policy}\n\\(z = z ∨ ¬ (z = z)\\).\n\\begin{{proof}}\nClose the goal with \\(em(z = z)\\).\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
        ),
    );
    project.relock();
    project
}

/// The shared axiom-policy violation: the `em` fixture under an
/// insufficient allow-list (SPEC.md §29.6 mutation 4).
pub fn axioms_insufficient() -> &'static (P, LexLeanError) {
    static FIXTURE: OnceLock<(P, LexLeanError)> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let _guard = env_lock();
        let project = em_project("\\allowaxioms{Classical.choice}");
        let error = project
            .engine()
            .verify(VerifyRequest {
                selection: Selection::Entrypoints,
            })
            .err()
            .expect("an insufficient allow-list fails policy checking");
        (project, error)
    })
}

/// Entry text for a fixture proof constant named `nzz` with a fixed
/// numeral-free signature, denoting `lean_name`.
#[must_use]
pub fn nzz_entry(lean_name: &str) -> String {
    format!(
        r#"spec = "lexlean/entry/1"
id = "nzz"
category = "proof-constant"
signature = "(pi ((explicit n (const lexlean.std.nat::nat))) (app (const lexlean.core::lnot) (app (const lexlean.std.nat::ne) (local n) (local n))))"
surface_arity = 1
frame = "call"

[denotation]
kind = "lean"
module = "Init"
name = "{lean_name}"

[[form]]
id = "nzz"
channel = "math"
surface = "nzz"
canonical_source = true
features = []

[render]
math = "(seq (operator-name nzz) (paren (slot 0)))"
"#
    )
}

/// A module whose proof cites the `nzz` proof constant; `extra_glossary`
/// rows come after the std.nat row.
#[must_use]
pub fn nzz_module(extra_glossaries: &[&str]) -> String {
    let mut uses = String::new();
    for glossary in extra_glossaries {
        uses.push_str(&format!("\\useglossary{{{glossary}}}\n"));
    }
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n{uses}\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{not-ne}}\n\\noaxioms\n\\(¬ (z ≠ z)\\).\n\\begin{{proof}}\nClose the goal with \\(nzz(z)\\).\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

/// The definitions fixture package: one type, term, and predicate entry
/// with document denotations into `Main`.
#[must_use]
pub fn defs_entries() -> Vec<(&'static str, String)> {
    let count = r#"spec = "lexlean/entry/1"
id = "count"
category = "type-noun"
signature = "(sort (type 0))"
surface_arity = 0
frame = "atom"

[denotation]
kind = "document"
module = "Main"
component = "count"

[[form]]
id = "count"
channel = "text"
surface = "count"
canonical_source = true
features = ["article-a", "lower-case", "singular"]
"#;
    let double = r#"spec = "lexlean/entry/1"
id = "double"
category = "function"
signature = "(pi ((explicit n (const lexlean.std.nat::nat))) (const lexlean.std.nat::nat))"
surface_arity = 1
frame = "call"

[denotation]
kind = "document"
module = "Main"
component = "double"

[[form]]
id = "double"
channel = "math"
surface = "double"
canonical_source = true
features = []

[render]
math = "(seq (operator-name double) (paren (slot 0)))"
"#;
    let good = r#"spec = "lexlean/entry/1"
id = "good"
category = "predicate-constant"
signature = "(sort prop)"
surface_arity = 0
frame = "atom"

[denotation]
kind = "document"
module = "Main"
component = "good"

[[form]]
id = "good"
channel = "math"
surface = "good"
canonical_source = true
features = []

[render]
math = "(operator-name good)"
"#;
    vec![
        ("count.toml", count.to_owned()),
        ("double.toml", double.to_owned()),
        ("good.toml", good.to_owned()),
    ]
}

/// The definitions fixture module: a type, term, and predicate definition
/// plus the literal theorem.
pub const DEFS_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.defs@1.0.0}\n\\title{Natural number addition}\n\n\\begin{typedefinition}{count}{test.defs::count}\n\\noaxioms\nA count is defined as \\(ℕ\\).\n\\end{typedefinition}\n\n\\begin{termdefinition}{double}{test.defs::double}\n\\noaxioms\nFor every natural number \\(n\\), \\(double(n)\\) is defined as \\(n + n\\).\n\\end{termdefinition}\n\n\\begin{predicatedefinition}{good}{test.defs::good}\n\\noaxioms\n\\(good\\) holds exactly when there exists a natural number \\(k\\) such that \\(k = k\\).\n\\end{predicatedefinition}\n\n\\begin{theorem}{add-zero}\n\\noaxioms\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";

/// A project containing the three definition kinds.
#[must_use]
pub fn defs_project() -> P {
    let project = P::example();
    let entries = defs_entries();
    let entry_refs: Vec<(&str, &str)> = entries
        .iter()
        .map(|(name, text)| (*name, text.as_str()))
        .collect();
    project.add_package(
        "lexicons/test-defs",
        "test.defs",
        &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
        &entry_refs,
    );
    project.write("src/Main.lex.tex", DEFS_MODULE);
    project.relock();
    project
}

/// Relative paths of every file under a directory.
#[must_use]
pub fn file_set(root: &Utf8Path) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for entry in walkdir::WalkDir::new(root.as_std_path())
        .into_iter()
        .flatten()
    {
        if entry.file_type().is_file() {
            out.insert(
                entry
                    .path()
                    .strip_prefix(root.as_std_path())
                    .expect("under root")
                    .to_string_lossy()
                    .replace('\\', "/"),
            );
        }
    }
    out
}

/// The checked project for a fixture, through the internal pipeline.
pub fn checked_project(project: &P) -> lexlean::link::CheckedProject {
    let inner =
        lexlean::project::Project::load(&project.root.join("lexlean.toml")).expect("project loads");
    let (lock, packages) = lexlean::lock::read_current_lock(&inner).expect("lock current");
    lexlean::link::check_project(&inner, &Selection::Entrypoints, &lock, packages)
        .expect("check_project")
}

/// The rendered build for a fixture (no Lean, no publication).
pub fn rendered(project: &P) -> lexlean::api::RenderedBuild {
    let inner =
        lexlean::project::Project::load(&project.root.join("lexlean.toml")).expect("project loads");
    let (lock, packages) = lexlean::lock::read_current_lock(&inner).expect("lock current");
    let checked = lexlean::link::check_project(&inner, &Selection::Entrypoints, &lock, packages)
        .expect("check_project");
    lexlean::api::render_build(&inner, &checked).expect("render_build")
}

/// The generated Lean text of one module from a rendered build.
#[must_use]
pub fn lean_text(build: &lexlean::api::RenderedBuild, module: &str) -> String {
    build
        .modules
        .iter()
        .find(|m| m.module == module)
        .unwrap_or_else(|| panic!("module {module} in build"))
        .lean_text
        .clone()
}

/// The canonical LaTeX text of one module from a rendered build.
#[must_use]
pub fn tex_text(build: &lexlean::api::RenderedBuild, module: &str) -> String {
    build
        .modules
        .iter()
        .find(|m| m.module == module)
        .unwrap_or_else(|| panic!("module {module} in build"))
        .tex_text
        .clone()
}

// ---- WS-E1 helpers (fixture runner, host gate, fake toolchains) ----

impl P {
    /// An empty temporary project directory (the fixture runner fills it).
    #[must_use]
    pub fn empty() -> Self {
        let temp = tempfile::Builder::new()
            .prefix("lexlean-fixture-")
            .tempdir()
            .expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).expect("utf8 tempdir");
        Self { temp, root }
    }
}

/// The real elan home: `ELAN_HOME` is deliberately ignored because a
/// concurrent test may hold the environment lock with a fake value; the
/// pinned toolchain lives under the home elan directory.
#[must_use]
pub fn real_elan_home() -> std::path::PathBuf {
    let home = std::env::var_os("HOME")
        .or_else(|| std::env::var_os("USERPROFILE"))
        .expect("HOME");
    std::path::PathBuf::from(home).join(".elan")
}

/// The pinned toolchain's mangled directory name under `toolchains/`.
#[must_use]
pub fn mangled_toolchain_name() -> String {
    lexlean::LEAN_TOOLCHAIN
        .replace('/', "--")
        .replace(':', "---")
}

/// Is the pinned toolchain installed in the real elan home?
#[must_use]
pub fn lean_host_available() -> bool {
    let bin = real_elan_home()
        .join("toolchains")
        .join(mangled_toolchain_name())
        .join("bin");
    bin.join("lean").is_file() || bin.join("lean.exe").is_file()
}

/// Is this the normative host (SPEC.md §8.3: Linux x86-64)?
#[must_use]
pub fn normative_host() -> bool {
    cfg!(all(target_os = "linux", target_arch = "x86_64"))
}

/// The host gate for Lean-backed cases: on the normative host the pinned
/// toolchain must be present (the case panics otherwise, R2: a vacuous
/// pass there is dishonest); on any other host without the toolchain the
/// case runs only its platform-independent assertions and says so.
#[must_use]
pub fn lean_backed(id: &str) -> bool {
    if lean_host_available() {
        return true;
    }
    assert!(
        !normative_host(),
        "{id}: the normative host (Linux x86-64) must have leanprover/lean4:v4.32.1 installed; a Lean-backed case never passes vacuously here (§8.3)"
    );
    eprintln!(
        "{id}: platform-bound host without the pinned toolchain; only the platform-independent assertions ran (§8.3)"
    );
    false
}

/// Build a fake elan home whose pinned toolchain mirrors the real one by
/// symlink but replaces the named executables under `bin/` with the given
/// bytes (made executable). Returns the fake home root.
#[must_use]
pub fn fake_elan_home(replacements: &[(String, Vec<u8>)]) -> tempfile::TempDir {
    let mangled = mangled_toolchain_name();
    let real_toolchain = real_elan_home().join("toolchains").join(&mangled);
    let fake = tempfile::Builder::new()
        .prefix("lexlean-fake-elan-")
        .tempdir()
        .expect("tempdir");
    let fake_toolchain_dir = fake.path().join("toolchains").join(&mangled);
    let fake_bin = fake_toolchain_dir.join("bin");
    std::fs::create_dir_all(&fake_bin).expect("mkdir");
    for entry in std::fs::read_dir(&real_toolchain)
        .expect("the pinned toolchain is installed")
        .flatten()
    {
        if entry.file_name() == "bin" {
            continue;
        }
        symlink_any(&entry.path(), &fake_toolchain_dir.join(entry.file_name()));
    }
    for entry in std::fs::read_dir(real_toolchain.join("bin"))
        .expect("real bin")
        .flatten()
    {
        let name = entry.file_name().to_string_lossy().into_owned();
        if replacements.iter().any(|(replaced, _)| *replaced == name) {
            continue;
        }
        symlink_any(&entry.path(), &fake_bin.join(&name));
    }
    for (name, bytes) in replacements {
        let path = fake_bin.join(name);
        std::fs::write(&path, bytes).expect("script");
        make_executable(&path);
    }
    fake
}

/// A fake elan home from `(name, script text)` pairs.
#[must_use]
pub fn fake_toolchain(replacements: &[(&str, &str)]) -> tempfile::TempDir {
    let owned: Vec<(String, Vec<u8>)> = replacements
        .iter()
        .map(|(name, script)| ((*name).to_owned(), script.as_bytes().to_vec()))
        .collect();
    fake_elan_home(&owned)
}

fn symlink_any(target: &Path, link: &Path) {
    #[cfg(unix)]
    std::os::unix::fs::symlink(target, link).expect("symlink");
    #[cfg(windows)]
    {
        if target.is_dir() {
            std::os::windows::fs::symlink_dir(target, link).expect("symlink");
        } else {
            std::os::windows::fs::symlink_file(target, link).expect("symlink");
        }
    }
}

fn make_executable(path: &Path) {
    #[cfg(unix)]
    {
        let mut permissions = std::fs::metadata(path).expect("stat").permissions();
        std::os::unix::fs::PermissionsExt::set_mode(&mut permissions, 0o755);
        std::fs::set_permissions(path, permissions).expect("chmod");
    }
    #[cfg(not(unix))]
    let _ = path;
}

/// The committed schema `schemas/<name>.schema.json`, parsed.
#[must_use]
pub fn schema(name: &str) -> serde_json::Value {
    let path = repo_root()
        .join("schemas")
        .join(format!("{name}.schema.json"));
    serde_json::from_slice(&std::fs::read(path.as_std_path()).expect("schema exists"))
        .expect("schema parses")
}

/// Assert `instance` validates against `schemas/<name>.schema.json`,
/// naming `what` on failure (§30.4: schemas are exercised).
pub fn assert_schema(name: &str, what: &str, instance: &serde_json::Value) {
    let violations = crate::schema::validate(&schema(name), instance);
    assert!(
        violations.is_empty(),
        "{what} violates schemas/{name}.schema.json:\n{}",
        violations
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// Assert a JSON file validates against a schema.
pub fn assert_json_file_schema(name: &str, path: &Utf8Path) {
    let value: serde_json::Value =
        serde_json::from_slice(&std::fs::read(path.as_std_path()).expect("json file"))
            .unwrap_or_else(|error| panic!("{path}: {error}"));
    assert_schema(name, path.as_str(), &value);
}

/// Assert a TOML file, converted to JSON, validates against a schema.
pub fn assert_toml_file_schema(name: &str, path: &Utf8Path) {
    let text = std::fs::read_to_string(path.as_std_path()).expect("toml file");
    let value: toml::Value = text
        .parse()
        .unwrap_or_else(|error| panic!("{path}: {error}"));
    let json = serde_json::to_value(&value).expect("toml converts to json");
    assert_schema(name, path.as_str(), &json);
}

/// A `lake` wrapper script that behaves as the pinned lake except that,
/// for `lake env lean` on a path matching `glob_fragment`, it prints
/// `injected` to the named stream first (`stdout` or `stderr`) and then
/// runs the real command; with `replace = true` it prints and exits 0
/// without running lean. The real lake is found through the sibling
/// `lean` symlink of the fake bin directory.
#[must_use]
pub fn lake_wrapper(glob_fragment: &str, injected: &str, stream: &str, replace: bool) -> String {
    let redirect = if stream == "stderr" { " >&2" } else { "" };
    let tail = if replace { "exit 0" } else { "" };
    format!(
        "#!/bin/sh\nreal=\"$(dirname \"$(readlink -f \"$(dirname \"$0\")/lean\")\")/lake\"\nif [ \"$1\" = \"env\" ] && [ \"$2\" = \"lean\" ]; then\n  for argument in \"$@\"; do\n    case \"$argument\" in\n      {glob_fragment})\n        printf '%s\\n' '{injected}'{redirect}\n        {tail}\n        ;;\n    esac\n  done\nfi\nexec \"$real\" \"$@\"\n"
    )
}

/// §30.3 "crate package", RP-12: package the shipped crate, extract the
/// `.crate`, build it offline in isolation, and return the packaged
/// binary's `--version` text. The build reuses `target/package-verify`
/// (never the workspace build directory, which the running test holds).
///
/// # Errors
///
/// Any step failing, with the captured output.
pub fn packaged_crate_version(root: &Utf8Path) -> Result<String, String> {
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_owned());
    let target_dir = root.join("target/package-verify");
    let run = |program: &str, args: &[&str], cwd: &Utf8Path, envs: &[(&str, &str)]| {
        let mut command = std::process::Command::new(program);
        command.args(args).current_dir(cwd.as_std_path());
        for (key, value) in envs {
            command.env(key, value);
        }
        let output = command
            .output()
            .map_err(|error| format!("{program} {}: {error}", args.join(" ")))?;
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        if !output.status.success() {
            return Err(format!(
                "{program} {} exited {:?}\n{stdout}\n{stderr}",
                args.join(" "),
                output.status.code()
            ));
        }
        Ok(stdout)
    };
    run(
        &cargo,
        &[
            "package",
            "-p",
            "lexlean",
            "--no-verify",
            "--allow-dirty",
            "--offline",
            "--target-dir",
            target_dir.as_str(),
        ],
        root,
        &[],
    )?;
    let package_dir = target_dir.join("package");
    let crate_file = std::fs::read_dir(package_dir.as_std_path())
        .map_err(|error| format!("{package_dir}: {error}"))?
        .flatten()
        .map(|entry| entry.path())
        .find(|path| {
            path.extension()
                .is_some_and(|extension| extension == "crate")
                && path
                    .file_name()
                    .is_some_and(|name| name.to_string_lossy().starts_with("lexlean-"))
        })
        .ok_or_else(|| format!("{package_dir}: no lexlean-*.crate was produced"))?;
    let extract = tempfile::Builder::new()
        .prefix("lexlean-package-")
        .tempdir()
        .map_err(|error| error.to_string())?;
    let extract_dir = Utf8PathBuf::from_path_buf(extract.path().to_path_buf())
        .map_err(|_| "non-UTF-8 temporary directory".to_owned())?;
    run(
        "tar",
        &["xzf", &crate_file.to_string_lossy()],
        &extract_dir,
        &[],
    )?;
    let unpacked = std::fs::read_dir(extract_dir.as_std_path())
        .map_err(|error| error.to_string())?
        .flatten()
        .map(|entry| entry.path())
        .find(|path| path.is_dir())
        .ok_or("the crate archive unpacked nothing")?;
    let unpacked = Utf8PathBuf::from_path_buf(unpacked).map_err(|_| "non-UTF-8 path".to_owned())?;
    for required in [
        "language",
        "schemas",
        "tests/golden",
        "model/errors.toml",
        "build.rs",
    ] {
        if !unpacked.join(required).as_std_path().exists() {
            return Err(format!(
                "the packaged crate lacks `{required}`; the normative data must ship inside the crate (§7, §21.2)"
            ));
        }
    }
    // Debug info is not part of the identity being compared; leaving it out
    // keeps the isolated build directory small.
    run(
        &cargo,
        &["build", "--offline", "--bin", "lexlean"],
        &unpacked,
        &[
            ("CARGO_TARGET_DIR", target_dir.as_str()),
            ("CARGO_PROFILE_DEV_DEBUG", "0"),
        ],
    )?;
    let binary = target_dir.join("debug").join(if cfg!(windows) {
        "lexlean.exe"
    } else {
        "lexlean"
    });
    run(binary.as_str(), &["--version"], &unpacked, &[])
}

/// Run the pinned `lean` on a tiny module with `#print axioms` commands and
/// return `(the successful output, the output of a run whose fourth command
/// names an unknown constant)`, both normalized to LF. Requires the pinned
/// toolchain (callers gate on [`lean_backed`]).
#[must_use]
pub fn print_axioms_output() -> (String, String) {
    let lean = real_elan_home()
        .join("toolchains")
        .join(mangled_toolchain_name())
        .join("bin")
        .join("lean");
    let dir = tempfile::Builder::new()
        .prefix("lexlean-axioms-")
        .tempdir()
        .expect("tempdir");
    let body = "module\nimport Init\nnamespace Demo.M\npublic theorem no_ax (n : Nat) : n = n := rfl\npublic theorem uses_choice (p : Prop) : p ∨ ¬ p := Classical.em p\npublic theorem uses_funext (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := funext h\nend Demo.M\n#print axioms Demo.M.no_ax\n#print axioms Demo.M.uses_choice\n#print axioms Demo.M.uses_funext\n";
    let run = |name: &str, text: &str| {
        let path = dir.path().join(name);
        std::fs::write(&path, text).expect("write module");
        let output = std::process::Command::new(&lean)
            .arg(&path)
            .current_dir(dir.path())
            .env("LEAN_PATH", "")
            .output()
            .expect("the pinned lean runs");
        String::from_utf8_lossy(&output.stdout)
            .replace("\r\n", "\n")
            .replace(dir.path().to_string_lossy().as_ref(), "$STAGING")
    };
    let good = run("Good.lean", body);
    let bad = run("Bad.lean", &format!("{body}#print axioms Demo.M.missing\n"));
    (good, bad)
}
