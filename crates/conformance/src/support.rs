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

// ---- WS-C (config / CLI / security) helpers ----

/// The explicit resource policy of a fixture project, for driving the
/// child runner directly.
#[must_use]
pub fn limits_of(project: &P) -> lexlean::config::Limits {
    lexlean::project::Project::load(&project.root.join("lexlean.toml"))
        .expect("project loads")
        .config
        .limits
}

/// Create a symbolic link on any supported host (§8.3): Unix has one
/// symlink kind; Windows distinguishes directory and file links.
pub fn symlink_any(target: impl AsRef<Path>, link: impl AsRef<Path>) {
    #[cfg(unix)]
    std::os::unix::fs::symlink(target, link).expect("symlink");
    #[cfg(windows)]
    {
        if target.as_ref().is_dir() {
            std::os::windows::fs::symlink_dir(target, link).expect("symlink");
        } else {
            std::os::windows::fs::symlink_file(target, link).expect("symlink");
        }
    }
}

// ---- WS-D helpers ----

/// A label-word entry with one canonical text form spelling `surface`.
#[must_use]
pub fn label_word_entry(id: &str, surface: &str) -> String {
    let features = if surface.chars().next().is_some_and(char::is_uppercase) {
        "[\"sentence-case\", \"singular\"]"
    } else {
        "[\"lower-case\", \"singular\"]"
    };
    format!(
        r#"spec = "lexlean/entry/1"
id = "{id}"
category = "label-word"
surface_arity = 0
frame = "atom"

[denotation]
kind = "defined"
value = "(const lexlean.std.nat::add)"

[[form]]
id = "{id}"
channel = "text"
surface = "{surface}"
canonical_source = true
features = {features}
"#
    )
}

/// An adjective-predicate entry over natural numbers, defined as `n = n`,
/// with one canonical text form spelling `surface`.
#[must_use]
pub fn adjective_entry(id: &str, surface: &str) -> String {
    format!(
        r#"spec = "lexlean/entry/1"
id = "{id}"
category = "adjective-predicate"
signature = "(pi ((explicit n (const lexlean.std.nat::nat))) (sort prop))"
surface_arity = 1
frame = "adjective"

[denotation]
kind = "defined"
value = "(lam ((explicit n (const lexlean.std.nat::nat))) (app (const lexlean.core::eq) (local n) (local n)))"

[[form]]
id = "{id}"
channel = "text"
surface = "{surface}"
canonical_source = true
features = ["lower-case"]
"#
    )
}

// ---- WS-A helpers: the Lean-verified proof corpus ----

/// One fixture entry of the corpus package: `(file name, TOML text)`.
type FixtureEntry = (&'static str, String);

/// A proof-constant entry over `Init` with an explicit LSE signature.
fn corpus_proof_constant(id: &str, surface: &str, signature: &str, lean_name: &str) -> String {
    let arity = signature.matches("(explicit ").count();
    let slots: Vec<String> = (0..arity).map(|index| format!("(slot {index})")).collect();
    let arguments = if arity == 1 {
        slots[0].clone()
    } else {
        format!("(seq {})", slots.join(" (space) "))
    };
    format!(
        r#"spec = "lexlean/entry/1"
id = "{id}"
category = "proof-constant"
signature = "{signature}"
surface_arity = {arity}
frame = "call"

[denotation]
kind = "lean"
module = "Init"
name = "{lean_name}"

[[form]]
id = "{id}"
channel = "math"
surface = "{surface}"
canonical_source = true
features = []

[render]
math = "(seq (operator-name {surface}) (paren {arguments}))"
"#
    )
}

/// The `test.corpus` fixture package: `Init` proof constants whose
/// signatures carry numerals (`Nat.zero_add`) and quantified equations
/// (`Nat.add_comm`), document-denoting `even` (adjective predicate) and
/// `double` (noun function) entries, and glossary-declared structures with
/// eliminator descriptors mirroring `Or` (`disj`) and `And` (`conj`) so
/// cases on a hypothesis and constructor over a structure are exercised.
#[must_use]
pub fn corpus_entries() -> Vec<FixtureEntry> {
    let nat = "(const lexlean.std.nat::nat)";
    let zeroadd = corpus_proof_constant(
        "zeroadd",
        "zeroadd",
        &format!("(pi ((explicit n {nat})) (app (const lexlean.core::eq) (app (const lexlean.std.nat::add) (nat 0) (local n)) (local n)))"),
        "Nat.zero_add",
    );
    let addcomm = corpus_proof_constant(
        "addcomm",
        "addcomm",
        &format!("(pi ((explicit n {nat}) (explicit m {nat})) (app (const lexlean.core::eq) (app (const lexlean.std.nat::add) (local n) (local m)) (app (const lexlean.std.nat::add) (local m) (local n))))"),
        "Nat.add_comm",
    );
    let even = format!(
        r#"spec = "lexlean/entry/1"
id = "even"
category = "adjective-predicate"
signature = "(pi ((explicit n {nat})) (sort prop))"
surface_arity = 1
frame = "adjective"

[denotation]
kind = "document"
module = "Main"
component = "even"

[[form]]
id = "even"
channel = "text"
surface = "even"
canonical_source = true
features = ["lower-case"]
"#
    );
    let double = format!(
        r#"spec = "lexlean/entry/1"
id = "double"
category = "noun-function"
signature = "(pi ((explicit n {nat})) {nat})"
surface_arity = 1
frame = "noun-of"

[denotation]
kind = "document"
module = "Main"
component = "double"

[[form]]
id = "double"
channel = "text"
surface = "double"
canonical_source = true
features = ["lower-case", "singular"]
"#
    );
    let structure = |id: &str, text: &str, lean: &str, ctors: &str| {
        format!(
            r#"spec = "lexlean/entry/1"
id = "{id}"
category = "function"
signature = "(pi ((explicit p (sort prop)) (explicit q (sort prop))) (sort prop))"
surface_arity = 2
frame = "call"

[denotation]
kind = "lean"
module = "Init"
name = "{lean}"

[[form]]
id = "{id}-text"
channel = "text"
surface = "{text}"
canonical_source = true
features = ["article-a", "lower-case", "singular"]

[[form]]
id = "{id}"
channel = "math"
surface = "{id}"
canonical_source = true
features = []

[render]
math = "(seq (operator-name {id}) (paren (seq (slot 0) (token comma) (space) (slot 1))))"

[eliminator]
cases_lean_name = "{lean}.casesOn"
induction_lean_name = "{lean}.rec"
{ctors}"#
        )
    };
    let disj = structure(
        "disj",
        "disjunction",
        "Or",
        "\n[[eliminator.constructor]]\nentry = \"test.corpus::disj-inl\"\nlean_name = \"Or.inl\"\nfields = [\"h\"]\ninduction_hypotheses = []\n\n[[eliminator.constructor]]\nentry = \"test.corpus::disj-inr\"\nlean_name = \"Or.inr\"\nfields = [\"h\"]\ninduction_hypotheses = []\n",
    );
    let conj = structure(
        "conj",
        "conjunction",
        "And",
        "\n[[eliminator.constructor]]\nentry = \"test.corpus::conj-intro\"\nlean_name = \"And.intro\"\nfields = [\"left\", \"right\"]\ninduction_hypotheses = []\n",
    );
    let inl = corpus_proof_constant(
        "disj-inl",
        "inl",
        "(pi ((implicit a (sort prop)) (implicit b (sort prop)) (explicit h (local a))) (app (const test.corpus::disj) (local a) (local b)))",
        "Or.inl",
    );
    let inr = corpus_proof_constant(
        "disj-inr",
        "inr",
        "(pi ((implicit a (sort prop)) (implicit b (sort prop)) (explicit h (local b))) (app (const test.corpus::disj) (local a) (local b)))",
        "Or.inr",
    );
    let intro = corpus_proof_constant(
        "conj-intro",
        "cintro",
        "(pi ((implicit a (sort prop)) (implicit b (sort prop)) (explicit left (local a)) (explicit right (local b))) (app (const test.corpus::conj) (local a) (local b)))",
        "And.intro",
    );
    let combine = format!(
        r#"spec = "lexlean/entry/1"
id = "combine"
category = "function"
signature = "(pi ((explicit a {nat}) (explicit b {nat})) {nat})"
surface_arity = 2
frame = "call"

[denotation]
kind = "document"
module = "Main"
component = "combine"

[[form]]
id = "combine"
channel = "math"
surface = "combine"
canonical_source = true
features = []

[render]
math = "(seq (operator-name combine) (paren (seq (slot 0) (space) (slot 1))))"
"#
    );
    vec![
        ("zeroadd.toml", zeroadd),
        ("addcomm.toml", addcomm),
        ("combine.toml", combine),
        ("even.toml", even),
        ("double.toml", double),
        ("disj.toml", disj),
        ("conj.toml", conj),
        ("disj-inl.toml", inl),
        ("disj-inr.toml", inr),
        ("conj-intro.toml", intro),
    ]
}

/// The corpus module: one multi-theorem module exercising every §16.2
/// simple sentence, have, rewrite (forward and backward, at goal and at a
/// hypothesis), simplify (goal and hypothesis), structured apply with two
/// premises, constructor (conjunction, biconditional, and a glossary
/// structure), cases and induction on `Nat`, cases on a hypothesis,
/// calculate with two steps, every §15.6 connective and quantifier, section
/// parameters referenced inside and outside their section, and definitions
/// with predicate-frame and noun-of self heads.
pub const CORPUS_MODULE: &str = r"\begin{lexlean}{Main}
\useglossary{lexlean.std.nat@1.0.0}
\useglossary{test.corpus@1.0.0}
\title{Natural number addition}

\begin{predicatedefinition}{even}{test.corpus::even}
\noaxioms
For every natural number \(n\), \(n\) is even holds exactly when there exists a natural number \(k\) such that \(n = k + k\).
\end{predicatedefinition}

\begin{termdefinition}{double}{test.corpus::double}
\noaxioms
For every natural number \(n\), the double of \(n\) is defined as \(n + n\).
\end{termdefinition}

\begin{termdefinition}{combine}{test.corpus::combine}
\noaxioms
For every natural number \(a\); natural number \(b\), \(combine(a, b)\) is defined as \(a + b\).
\end{termdefinition}

\begin{theorem}{nested-call}
\noaxioms
For every natural number \(a\) and natural number \(b\), \(succ(a) + combine((b + 0), a) = combine((b + 0), a) + succ(a)\).
\begin{proof}
Close the goal with \(addcomm(succ(a), combine((b + 0), a))\).
\end{proof}
\end{theorem}

\begin{theorem}{add-zero}
\noaxioms
For every natural number \(m\), \(m + 0 = m\).
\begin{proof}
Close the goal by reflexivity.
\end{proof}
\end{theorem}

\begin{theorem}{add-succ}
\noaxioms
For every natural number \(a\) and natural number \(b\), \(a + succ(b) = succ(a + b)\).
\begin{proof}
Close the goal by reflexivity.
\end{proof}
\end{theorem}

\begin{lemma}{succ-congr}
\noaxioms
For every natural number \(a\) and natural number \(b\), if \(a = b\), then \(succ(a) = succ(b)\).
\begin{proof}
Assume \(h\).
\begin{rewrite}{goal}
\forward{h}
\end{rewrite}
\end{proof}
\end{lemma}

\begin{theorem}{zero-add}
\noaxioms
For every natural number \(n\), \(0 + n = n\).
\begin{proof}
\begin{induction}{n}
\begin{case}{lexlean.std.nat::zero}
\bind{}
Close the goal by reflexivity.
\end{case}
\begin{case}{lexlean.std.nat::succ}
\bind{m;ih}
\begin{rewrite}{goal}
\forward{\reference{Main::add-succ}}
\end{rewrite}
Apply \(\reference{Main::succ-congr}\).
Close the goal with \(ih\).
\end{case}
\end{induction}
\end{proof}
\end{theorem}

\begin{theorem}{apply-known}
\noaxioms
For every natural number \(n\), \(succ(0 + n) = succ(n)\).
\begin{proof}
Apply \(\reference{Main::succ-congr}\).
Close the goal with \(\reference{Main::zero-add}(n)\).
\end{proof}
\end{theorem}

\begin{theorem}{init-zero-add}
\noaxioms
For every natural number \(n\), \(0 + n = n\).
\begin{proof}
Close the goal with \(zeroadd(n)\).
\end{proof}
\end{theorem}

\begin{theorem}{init-add-comm}
\noaxioms
For every natural number \(a\) and natural number \(b\), \(a + b = b + a\).
\begin{proof}
Close the goal with \(addcomm(a, b)\).
\end{proof}
\end{theorem}

\begin{theorem}{rewrite-hypothesis}
\noaxioms
For every natural number \(n\), if \(n + 0 = 1\), then \(n = 1\).
\begin{proof}
Assume \(h\).
\begin{rewrite}{h}
\forward{\reference{Main::add-zero}}
\end{rewrite}
Close the goal with \(h\).
\end{proof}
\end{theorem}

\begin{theorem}{rewrite-backward}
\noaxioms
For every natural number \(a\) and natural number \(b\), \(succ(a + b) = a + succ(b)\).
\begin{proof}
\begin{rewrite}{goal}
\backward{\reference{Main::add-succ}}
\end{rewrite}
\end{proof}
\end{theorem}

\begin{theorem}{implies-rewrite}
\noaxioms
For every natural number \(n\), \(n = 1\) implies \(n + 0 = 1\).
\begin{proof}
Assume \(h\).
\begin{rewrite}{goal}
\forward{\reference{Main::add-zero}}
\end{rewrite}
Close the goal with \(h\).
\end{proof}
\end{theorem}

\begin{theorem}{simplify-both}
\allowaxioms{propext}
For every natural number \(n\), if \(0 + n = 1\), then \(n + 0 = 1\).
\begin{proof}
Assume \(h\).
\begin{simplify}{h}
\rule{\reference{Main::zero-add}}
\end{simplify}
\begin{simplify}{goal}
\rule{\reference{Main::add-zero}}
\end{simplify}
Close the goal with \(h\).
\end{proof}
\end{theorem}

\begin{theorem}{simplify-closes}
\allowaxioms{propext}
For every natural number \(n\), if \(n = 1\), then \(n + 0 = 1\).
\begin{proof}
Assume \(h\).
\begin{simplify}{goal}
\rule{\reference{Main::add-zero}}
\rule{h}
\end{simplify}
\end{proof}
\end{theorem}

\begin{theorem}{have-step}
\noaxioms
For every natural number \(n\), \(0 + n = n + 0\).
\begin{proof}
\begin{have}{h}
\(0 + n = n\).
\begin{proof}
Close the goal with \(zeroadd(n)\).
\end{proof}
\end{have}
\begin{rewrite}{goal}
\forward{h}
\forward{\reference{Main::add-zero}}
\end{rewrite}
\end{proof}
\end{theorem}

\begin{lemma}{two-premises}
\noaxioms
For every natural number \(n\), if \(n = n\), then if \(0 + n = n\), then \(n + 0 = n\).
\begin{proof}
Assume \(h\).
Assume \(g\).
Close the goal by reflexivity.
\end{proof}
\end{lemma}

\begin{theorem}{structured-apply}
\noaxioms
For every natural number \(n\), \(n + 0 = n\).
\begin{proof}
\begin{apply}{\reference{Main::two-premises}}
\begin{premise}{1}
Close the goal by reflexivity.
\end{premise}
\begin{premise}{2}
Close the goal with \(zeroadd(n)\).
\end{premise}
\end{apply}
\end{proof}
\end{theorem}

\begin{theorem}{constructor-and}
\noaxioms
For every natural number \(n\), \(n + 0 = n\) and \(0 + n = n\).
\begin{proof}
\begin{constructor}
\begin{branch}{1}
Close the goal by reflexivity.
\end{branch}
\begin{branch}{2}
Close the goal with \(zeroadd(n)\).
\end{branch}
\end{constructor}
\end{proof}
\end{theorem}

\begin{theorem}{constructor-iff}
\noaxioms
For every natural number \(n\), \(n + 0 = n\) if and only if \(n = n\).
\begin{proof}
\begin{constructor}
\begin{branch}{1}
Assume \(h\).
Close the goal by reflexivity.
\end{branch}
\begin{branch}{2}
Assume \(h\).
Close the goal by reflexivity.
\end{branch}
\end{constructor}
\end{proof}
\end{theorem}

\begin{theorem}{constructor-structure}
\noaxioms
For every natural number \(n\), \(conj(n + 0 = n, 0 + n = n)\).
\begin{proof}
\begin{constructor}
\begin{branch}{1}
Close the goal by reflexivity.
\end{branch}
\begin{branch}{2}
Close the goal with \(zeroadd(n)\).
\end{branch}
\end{constructor}
\end{proof}
\end{theorem}

\begin{theorem}{cases-nat}
\noaxioms
For every natural number \(n\), \(n + 0 = n\) or \(n = 1\).
\begin{proof}
\begin{cases}{n}
\begin{case}{lexlean.std.nat::zero}
\bind{}
Select the left alternative.
Close the goal by reflexivity.
\end{case}
\begin{case}{lexlean.std.nat::succ}
\bind{m}
Select the left alternative.
Close the goal by reflexivity.
\end{case}
\end{cases}
\end{proof}
\end{theorem}

\begin{theorem}{or-comm}
\noaxioms
For every natural number \(n\), if \(disj(n = 0, n = 1)\), then \(disj(n = 1, n = 0)\).
\begin{proof}
Assume \(h\).
\begin{cases}{h}
\begin{case}{test.corpus::disj-inl}
\bind{x}
Select the right alternative.
Close the goal with \(x\).
\end{case}
\begin{case}{test.corpus::disj-inr}
\bind{y}
Select the left alternative.
Close the goal with \(y\).
\end{case}
\end{cases}
\end{proof}
\end{theorem}

\begin{theorem}{and-comm}
\noaxioms
For every natural number \(n\), if \(conj(n = 0, n + 0 = n)\), then \(conj(n + 0 = n, n = 0)\).
\begin{proof}
Assume \(h\).
\begin{cases}{h}
\begin{case}{test.corpus::conj-intro}
\bind{l;r}
\begin{constructor}
\begin{branch}{1}
Close the goal with \(r\).
\end{branch}
\begin{branch}{2}
Close the goal with \(l\).
\end{branch}
\end{constructor}
\end{case}
\end{cases}
\end{proof}
\end{theorem}

\begin{theorem}{not-both}
\noaxioms
For every natural number \(n\), not \(conj(n = n, ¬ (n = n))\).
\begin{proof}
Assume \(h\).
\begin{cases}{h}
\begin{case}{test.corpus::conj-intro}
\bind{l;r}
Apply \(r\).
Close the goal with \(l\).
\end{case}
\end{cases}
\end{proof}
\end{theorem}

\begin{theorem}{exists-witness}
\noaxioms
There exists a natural number \(k\) such that \(k + 0 = 0\).
\begin{proof}
Use \(0\) as the witness.
Close the goal by reflexivity.
\end{proof}
\end{theorem}

\begin{theorem}{exists-unique}
\noaxioms
There exists exactly one natural number \(k\) such that \(k = 0\).
\begin{proof}
Use \(0\) as the witness.
\begin{constructor}
\begin{branch}{1}
Close the goal by reflexivity.
\end{branch}
\begin{branch}{2}
Assume \(y\), \(h\).
Close the goal with \(h\).
\end{branch}
\end{constructor}
\end{proof}
\end{theorem}

\begin{theorem}{select-right}
\noaxioms
For every natural number \(n\), \(n = 1\) or \(n + 0 = n\).
\begin{proof}
Select the right alternative.
Close the goal by reflexivity.
\end{proof}
\end{theorem}

\begin{theorem}{calculation}
\noaxioms
For every natural number \(n\), \(0 + (n + 0) = n\).
\begin{proof}
\begin{calculate}
\start{0 + (n + 0)}
\step{lexlean.core::eq}{n + 0}{\reference{Main::zero-add}(n + 0)}
\step{lexlean.core::eq}{n}{\reference{Main::add-zero}(n)}
\end{calculate}
\end{proof}
\end{theorem}

\begin{theorem}{double-even}
\noaxioms
For every natural number \(n\), the double of \(n\) is even.
\begin{proof}
Use \(n\) as the witness.
Close the goal by reflexivity.
\end{proof}
\end{theorem}

\begin{theorem}{zero-even}
\noaxioms
\(0\) is even.
\begin{proof}
Use \(0\) as the witness.
Close the goal by reflexivity.
\end{proof}
\end{theorem}

\begin{section}{parameters}
\heading{Natural number addition}
\parameters{natural number \(p\)}
\begin{theorem}{param-add-zero}
\noaxioms
\(p + 0 = p\).
\begin{proof}
Close the goal by reflexivity.
\end{proof}
\end{theorem}

\begin{theorem}{use-inside}
\noaxioms
\(succ(p + 0) = succ(p)\).
\begin{proof}
Apply \(\reference{Main::succ-congr}\).
Close the goal with \(\reference{Main::param-add-zero}(p)\).
\end{proof}
\end{theorem}
\end{section}

\begin{corollary}{use-outside}
\noaxioms
For every natural number \(q\), \(q + 0 = q\).
\begin{proof}
Close the goal with \(\reference{Main::param-add-zero}(q)\).
\end{proof}
\end{corollary}
\end{lexlean}
";

/// A project holding the corpus module and its fixture package (relocked).
#[must_use]
pub fn corpus_project() -> P {
    let project = P::example();
    let entries = corpus_entries();
    let entry_refs: Vec<(&str, &str)> = entries
        .iter()
        .map(|(name, text)| (*name, text.as_str()))
        .collect();
    project.add_package(
        "lexicons/test-corpus",
        "test.corpus",
        &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
        &entry_refs,
    );
    project.write("src/Main.lex.tex", CORPUS_MODULE);
    project.relock();
    project
}

/// The one shared Lean-verified run of the proof corpus (C11): built and
/// verified with the pinned toolchain; the per-form assertions read its
/// generated Lean and attestation.
pub fn verified_corpus() -> &'static VerifiedFixture {
    static FIXTURE: OnceLock<VerifiedFixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let _guard = env_lock();
        let project = corpus_project();
        let outcome = project
            .engine()
            .verify(VerifyRequest {
                selection: Selection::Entrypoints,
            })
            .unwrap_or_else(|error| {
                panic!("the proof corpus verifies under pinned Lean 4.32.1: {error:#?}")
            });
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

/// The generated Lean text of the verified corpus module.
#[must_use]
pub fn corpus_lean() -> String {
    let fixture = verified_corpus();
    lean_text(&rendered(&fixture.project), "Main")
}

/// The generated Lean lines of one corpus declaration: from its `theorem`
/// or `def` line to the line before the next declaration or the closing
/// `end`, without trailing blank lines.
#[must_use]
pub fn corpus_declaration_lean(lean_name: &str) -> String {
    let lean = corpus_lean();
    let lines: Vec<&str> = lean.lines().collect();
    let start = lines
        .iter()
        .position(|line| {
            line.starts_with(&format!("public theorem {lean_name} "))
                || line.starts_with(&format!("@[expose] public def {lean_name} "))
        })
        .unwrap_or_else(|| panic!("`{lean_name}` in the corpus Lean:\n{lean}"));
    let end = lines[start + 1..]
        .iter()
        .position(|line| {
            line.starts_with("public ")
                || line.starts_with("@[expose] ")
                || line.starts_with("end ")
        })
        .map_or(lines.len(), |offset| start + 1 + offset);
    let mut block = lines[start..end].join("\n");
    while block.ends_with('\n') {
        block.pop();
    }
    block.trim_end().to_owned()
}

// ---- WS-B helpers ----
/// The proof-forms module: cases, right, induction, intro, structured apply
/// with a premise, and a one-step calculation, all Lean-verifiable.
pub const PROOF_FORMS_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{cases-goal}\n\\noaxioms\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\begin{proof}\n\\begin{cases}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nClose the goal by reflexivity.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m}\nClose the goal by reflexivity.\n\\end{case}\n\\end{cases}\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{right-goal}\n\\noaxioms\nFor every natural number \\(n\\), \\(n = 1\\) or \\(n + 0 = n\\).\n\\begin{proof}\nSelect the right alternative.\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{induction-goal}\n\\noaxioms\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\begin{proof}\n\\begin{induction}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nClose the goal by reflexivity.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m;ih}\nClose the goal by reflexivity.\n\\end{case}\n\\end{induction}\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{first}\n\\noaxioms\nIf \\(0 + 0 = 0\\), then \\(0 * 0 = 0\\).\n\\begin{proof}\nAssume \\(h\\).\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{apply-goal}\n\\noaxioms\n\\(0 * 0 = 0\\).\n\\begin{proof}\n\\begin{apply}{\\reference{Main::first}}\n\\begin{premise}{1}\nClose the goal by reflexivity.\n\\end{premise}\n\\end{apply}\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{zz}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{calc-goal}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\n\\begin{calculate}\n\\start{0 + 0}\n\\step{lexlean.core::eq}{0}{\\reference{Main::zz}}\n\\end{calculate}\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";

/// The exact generated Lean of [`PROOF_FORMS_MODULE`].
pub const PROOF_FORMS_LEAN: &str = "module\npublic import Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic theorem cases_goal (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  cases llv0 with\n    | zero =>\n      rfl\n    | succ llh0 =>\n      rfl\n\npublic theorem right_goal (llv0 : Nat) : Or (Eq llv0 (1 : Nat)) (Eq (Nat.add llv0 0) llv0) := by\n  right\n  rfl\n\npublic theorem induction_goal (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  induction llv0 with\n    | zero =>\n      rfl\n    | succ llh0 llh1 =>\n      rfl\n\npublic theorem first : (Eq (Nat.add 0 0) (0 : Nat)) → Eq (Nat.mul 0 0) (0 : Nat) := by\n  intro llh0\n  rfl\n\npublic theorem apply_goal : Eq (Nat.mul 0 0) (0 : Nat) := by\n  apply LexLeanExample.Main.first\n  rfl\n\npublic theorem zz : Eq (Nat.add 0 0) (0 : Nat) := by\n  rfl\n\npublic theorem calc_goal : Eq (Nat.add 0 0) (0 : Nat) := by\n  calc (Nat.add 0 0) = (0 : Nat) := LexLeanExample.Main.zz\n\nend LexLeanExample.Main\n";

/// The exact canonical LaTeX body (after `\\begin{document}`) of
/// [`PROOF_FORMS_MODULE`].
pub const PROOF_FORMS_TEX_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}\n\\begin{theorem}\n\\label{ll:main:cases-goal}\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\end{theorem}\n\\begin{proof}\nConsider the cases of \\(n\\).\nCase zero:\nThe goal follows by reflexivity.\nCase \\(succ\\) with \\(m\\):\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:right-goal}\nFor every natural number \\(n\\), \\(n = 1\\) or \\(n + 0 = n\\).\n\\end{theorem}\n\\begin{proof}\nSelect the right alternative.\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:induction-goal}\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\end{theorem}\n\\begin{proof}\nProceed by induction on \\(n\\).\nCase zero:\nThe goal follows by reflexivity.\nCase \\(succ\\) with \\(m\\), \\(ih\\):\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:first}\nIf \\(0 + 0 = 0\\), then \\(0 \\cdot 0 = 0\\).\n\\end{theorem}\n\\begin{proof}\nAssume \\(h\\).\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:apply-goal}\n\\(0 \\cdot 0 = 0\\).\n\\end{theorem}\n\\begin{proof}\nApply \\(\\texttt{Main::first}\\).\nPremise \\(1\\):\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:zz}\n\\(0 + 0 = 0\\).\n\\end{theorem}\n\\begin{proof}\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:calc-goal}\n\\(0 + 0 = 0\\).\n\\end{theorem}\n\\begin{proof}\n\\begin{align*}\n0 + 0 &= 0 && \\text{by } \\texttt{Main::zz}\n\\end{align*}\n\\end{proof}\n\\end{document}\n";

/// A three-level section nest with two parameters of which one is used.
pub const SECTIONS_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{section}{outer}\n\\heading{Natural number addition}\n\\parameters{natural number \\(p\\); natural number \\(q\\)}\n\\begin{section}{middle}\n\\heading{Natural number addition}\n\\begin{section}{inner}\n\\heading{Natural number addition}\n\\begin{theorem}{deep}\n\\noaxioms\n\\(q + 0 = q\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{section}\n\\end{section}\n\\end{section}\n\\end{lexlean}\n";

/// The exact generated Lean of [`SECTIONS_MODULE`].
pub const SECTIONS_LEAN: &str = "module\npublic import Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic theorem deep (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  rfl\n\nend LexLeanExample.Main\n";

/// The exact canonical LaTeX body of [`SECTIONS_MODULE`].
pub const SECTIONS_TEX_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}\n\\section{Natural number addition}\n\\label{ll:main:outer}\n\\[\\mathrm{Parameters}: \\forall p \\in \\mathbb{N}; \\forall q \\in \\mathbb{N}\\]\n\\subsection{Natural number addition}\n\\label{ll:main:middle}\n\\textbf{Natural number addition}\n\\label{ll:main:inner}\n\\begin{theorem}\n\\label{ll:main:deep}\n\\(q + 0 = q\\).\n\\end{theorem}\n\\begin{proof}\nThe goal follows by reflexivity.\n\\end{proof}\n\\end{document}\n";

/// The definitions fixture rendered exactly.
pub const DEFS_LEAN: &str = "module\npublic import Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\n@[expose] public def count : Type :=\n  Nat\n\n@[expose] public def double (llv0 : Nat) : Nat :=\n  Nat.add llv0 llv0\n\n@[expose] public def good : Prop :=\n  Exists (fun (llv0 : Nat) => Eq llv0 llv0)\n\npublic theorem add_zero (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  rfl\n\nend LexLeanExample.Main\n";

/// The exact canonical LaTeX body of [`DEFS_MODULE`].
pub const DEFS_TEX_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}\n\\begin{definition}\n\\label{ll:main:count}\nA count is defined as \\(\\mathbb{N}\\).\n\\end{definition}\n\\begin{definition}\n\\label{ll:main:double}\nFor every natural number \\(n\\), \\(\\operatorname{double}(n)\\) is defined as \\(n + n\\).\n\\end{definition}\n\\begin{definition}\n\\label{ll:main:good}\n\\(\\operatorname{good}\\) holds exactly when there exists a natural number \\(k\\) such that \\(k = k\\).\n\\end{definition}\n\\begin{theorem}\n\\label{ll:main:add-zero}\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\end{theorem}\n\\begin{proof}\nThe goal follows by reflexivity.\n\\end{proof}\n\\end{document}\n";

/// A unique-existence theorem over the `test.ext` fixture.
pub const UNIQUE_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.ext@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{unique}\n\\noaxioms\nThere exists exactly one natural number \\(k\\) such that \\(k = 0\\).\n\\begin{proof}\nUse \\(0\\) as the witness.\n\\begin{constructor}\n\\begin{branch}{1}\nClose the goal by reflexivity.\n\\end{branch}\n\\begin{branch}{2}\nAssume \\(y\\).\nAssume \\(h\\).\nClose the goal with \\(h\\).\n\\end{branch}\n\\end{constructor}\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";

/// The exact generated Lean of [`UNIQUE_MODULE`].
pub const UNIQUE_LEAN: &str = "module\npublic import Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic theorem unique : Exists (fun (llv0 : Nat) => And (Eq llv0 (0 : Nat)) ((llv1 : Nat) → (Eq llv1 (0 : Nat)) → Eq llv1 llv0)) := by\n  refine ⟨(0 : Nat), ?_⟩\n  constructor\n  rfl\n  intro llh0\n  intro llh1\n  exact llh1\n\nend LexLeanExample.Main\n";

/// The exact canonical LaTeX body of [`UNIQUE_MODULE`].
pub const UNIQUE_TEX_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}\n\\begin{theorem}\n\\label{ll:main:unique}\nThere exists exactly one natural number \\(k\\) such that \\(k = 0\\).\n\\end{theorem}\n\\begin{proof}\nUse \\(0\\) as the witness.\nBranch \\(1\\):\nThe goal follows by reflexivity.\nBranch \\(2\\):\nAssume \\(y\\).\nAssume \\(h\\).\nThe goal follows from \\(h\\).\n\\end{proof}\n\\end{document}\n";

/// A defined value reaching Lean constants (`two`).
pub const DEFINED_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.ext@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{twoeq}\n\\noaxioms\n\\(two = two\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";

/// The exact generated Lean of [`DEFINED_MODULE`].
pub const DEFINED_LEAN: &str = "module\npublic import Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic theorem twoeq : Eq (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero)) := by\n  rfl\n\nend LexLeanExample.Main\n";

/// LRE `sup`, `sub`, and `frac` renders.
pub const LRE_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.ext@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{sqhalf}\n\\noaxioms\nFor every natural number \\(n\\), \\(sq(n) = sq(n)\\) and \\(half(n) = half(n)\\).\n\\begin{proof}\n\\begin{constructor}\n\\begin{branch}{1}\nClose the goal by reflexivity.\n\\end{branch}\n\\begin{branch}{2}\nClose the goal by reflexivity.\n\\end{branch}\n\\end{constructor}\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";

/// The exact canonical LaTeX body of [`LRE_MODULE`].
pub const LRE_TEX_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}\n\\begin{theorem}\n\\label{ll:main:sqhalf}\nFor every natural number \\(n\\), \\({n}^{\\operatorname{two}} = {n}^{\\operatorname{two}}\\) and \\(\\frac{n}{{\\operatorname{h}}_{\\operatorname{i}}} = \\frac{n}{{\\operatorname{h}}_{\\operatorname{i}}}\\).\n\\end{theorem}\n\\begin{proof}\nBranch \\(1\\):\nThe goal follows by reflexivity.\nBranch \\(2\\):\nThe goal follows by reflexivity.\n\\end{proof}\n\\end{document}\n";

/// A section parameter whose type depends on an earlier parameter.
pub const DEPENDENT_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.ext@1.0.0}\n\\title{Natural number addition}\n\n\\begin{section}{outer}\n\\heading{Natural number addition}\n\\parameters{natural number \\(n\\); \\(fin(n)\\) \\(i\\)}\n\\begin{theorem}{dep}\n\\noaxioms\n\\(i = i\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{section}\n\\end{lexlean}\n";

/// The exact generated Lean of [`DEPENDENT_MODULE`].
pub const DEPENDENT_LEAN: &str = "module\npublic import Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic theorem dep (llv0 : Nat) (llv1 : Fin llv0) : Eq llv1 llv1 := by\n  rfl\n\nend LexLeanExample.Main\n";

/// The `test.ext` fixture entries: a universe-polymorphic proof constant
/// (`Eq.symm`), a numeral-bearing signature (`Nat.zero_add`), a defined
/// value reaching Lean constants, LRE sup/sub/frac renders, and a dependent
/// type function (`Fin`).
#[must_use]
pub fn ext_entries() -> Vec<(&'static str, &'static str)> {
    vec![
        ("eqsymm.toml", "spec = \"lexlean/entry/1\"\nid = \"eqsymm\"\ncategory = \"proof-constant\"\nsignature = \"(pi ((implicit a (sort (type u))) (implicit x (local a)) (implicit y (local a)) (explicit h (app (const lexlean.core::eq) (local x) (local y)))) (app (const lexlean.core::eq) (local y) (local x)))\"\nuniverses = [\"u\"]\nsurface_arity = 1\nframe = \"call\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Eq.symm\"\n\n[[form]]\nid = \"eqsymm\"\nchannel = \"math\"\nsurface = \"eqsymm\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(seq (operator-name eqsymm) (paren (slot 0)))\"\n"),
        ("fin.toml", "spec = \"lexlean/entry/1\"\nid = \"fin\"\ncategory = \"function\"\nsignature = \"(pi ((explicit n (const lexlean.std.nat::nat))) (sort (type 0)))\"\nsurface_arity = 1\nframe = \"call\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Fin\"\n\n[[form]]\nid = \"fin\"\nchannel = \"math\"\nsurface = \"fin\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(seq (operator-name fin) (paren (slot 0)))\"\n"),
        ("half.toml", "spec = \"lexlean/entry/1\"\nid = \"half\"\ncategory = \"function\"\nsignature = \"(pi ((explicit n (const lexlean.std.nat::nat))) (const lexlean.std.nat::nat))\"\nsurface_arity = 1\nframe = \"call\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Nat.pred\"\n\n[[form]]\nid = \"half\"\nchannel = \"math\"\nsurface = \"half\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(frac (slot 0) (sub (operator-name h) (operator-name i)))\"\n"),
        ("sq.toml", "spec = \"lexlean/entry/1\"\nid = \"sq\"\ncategory = \"function\"\nsignature = \"(pi ((explicit n (const lexlean.std.nat::nat))) (const lexlean.std.nat::nat))\"\nsurface_arity = 1\nframe = \"call\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Nat.succ\"\n\n[[form]]\nid = \"sq\"\nchannel = \"math\"\nsurface = \"sq\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(sup (slot 0) (operator-name two))\"\n"),
        ("two.toml", "spec = \"lexlean/entry/1\"\nid = \"two\"\ncategory = \"term-constant\"\nsignature = \"(const lexlean.std.nat::nat)\"\nsurface_arity = 0\nframe = \"atom\"\n\n[denotation]\nkind = \"defined\"\nvalue = \"(app (const lexlean.std.nat::succ) (app (const lexlean.std.nat::succ) (const lexlean.std.nat::zero)))\"\n\n[[form]]\nid = \"two\"\nchannel = \"both\"\nsurface = \"two\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(operator-name two)\"\n"),
        ("zeroadd.toml", "spec = \"lexlean/entry/1\"\nid = \"zeroadd\"\ncategory = \"proof-constant\"\nsignature = \"(pi ((explicit n (const lexlean.std.nat::nat))) (app (const lexlean.core::eq) (app (const lexlean.std.nat::add) (nat 0) (local n)) (local n)))\"\nsurface_arity = 1\nframe = \"call\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Nat.zero_add\"\n\n[[form]]\nid = \"zeroadd\"\nchannel = \"math\"\nsurface = \"zeroadd\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(seq (operator-name zeroadd) (paren (slot 0)))\"\n"),
    ]
}

/// A project registering the `test.ext` fixture package with `module` as
/// its entrypoint source.
#[must_use]
pub fn ext_project(module: &str) -> P {
    let project = P::example();
    project.add_package(
        "lexicons/test-ext",
        "test.ext",
        &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
        &ext_entries(),
    );
    project.write("src/Main.lex.tex", module);
    project.relock();
    project
}

/// Verify a project through the complete pipeline, expecting success, and
/// return the verified outcome. Real Lean runs.
pub fn verify_ok(project: &P) -> lexlean::VerifiedProject {
    let _guard = env_lock();
    project
        .engine()
        .verify(VerifyRequest {
            selection: Selection::Entrypoints,
        })
        .expect("the module verifies with real Lean")
}

/// The canonical LaTeX body after `\begin{document}` and its newline.
#[must_use]
pub fn tex_body(tex: &str) -> &str {
    tex.split_once("\\begin{document}\n")
        .map_or(tex, |(_, body)| body)
}

/// Generate the §18.8 probe module for the named `package::entry` external
/// entries of a project's closure and elaborate it with the pinned Lean
/// through `lake env` in the project's workspace. Returns the probe and the
/// process record. Real Lean runs.
pub fn probe_lean(
    project: &P,
    entries: &[&str],
) -> (
    lexlean::backend::lean::ProbeModule,
    lexlean::verify::child::ChildRecord,
) {
    use lexlean::lexicon::entry::Denotation;
    let checked = checked_project(project);
    let mut externals = std::collections::BTreeMap::new();
    for entry_id in entries {
        let qualified = lexlean::lexicon::lse::QualifiedId::parse(entry_id).expect("qualified");
        let entry = checked.closure.entry(&qualified).expect("the entry exists");
        let Denotation::Lean { module, name } = &entry.denotation else {
            panic!("{entry_id} is not a Lean entry");
        };
        externals.insert(
            (*entry_id).to_owned(),
            lexlean::ir::term::ExternalConstRef {
                package: qualified.package.clone(),
                entry: (*entry_id).to_owned(),
                lean_module: module.clone(),
                lean_name: name.clone(),
                signature_hash: entry.signature_hash.expect("a signature hash"),
            },
        );
    }
    let hex32: String = checked.semantic_id.to_hex()[..32].to_owned();
    let probe = lexlean::backend::lean::probe_module(&hex32, &externals, &checked.closure)
        .expect("probe renders");
    let _guard = env_lock();
    let toolchain = lexlean::verify::toolchain::preflight().expect("the pinned toolchain");
    let scratch = project.root.join(".lexlean/probe-scratch");
    std::fs::create_dir_all(scratch.as_std_path()).expect("scratch");
    let source = scratch.join(format!("{}.lean", probe.name));
    std::fs::write(source.as_std_path(), &probe.text).expect("write probe");
    let inner = lexlean::project::Project::load(&project.root.join("lexlean.toml")).expect("load");
    let normalizer = lexlean::verify::child::Normalizer::new(
        &scratch,
        &project.root,
        &project.root,
        &toolchain.root,
    );
    let bin = toolchain.root.join("bin");
    let record = lexlean::verify::child::run(
        &lexlean::verify::child::ChildSpec {
            tool: "lean",
            module: Some(probe.name.clone()),
            program: &toolchain.lake.path,
            executable_sha256: toolchain.lean.sha256,
            argv: vec!["env".to_owned(), "lean".to_owned(), source.to_string()],
            cwd: &project.root,
            extra_env: vec![("LEAN_PATH".to_owned(), scratch.to_string())],
            toolchain_bin: &bin,
        },
        &inner.config.limits,
        &normalizer,
    )
    .expect("lean runs");
    (probe, record)
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
        symlink_any(entry.path(), fake_toolchain_dir.join(entry.file_name()));
    }
    for entry in std::fs::read_dir(real_toolchain.join("bin"))
        .expect("real bin")
        .flatten()
    {
        let name = entry.file_name().to_string_lossy().into_owned();
        if replacements.iter().any(|(replaced, _)| *replaced == name) {
            continue;
        }
        symlink_any(entry.path(), fake_bin.join(&name));
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
    let body = "module\npublic import Init\nnamespace Demo.M\npublic theorem no_ax (n : Nat) : n = n := rfl\npublic theorem uses_choice (p : Prop) : p ∨ ¬ p := Classical.em p\npublic theorem uses_funext (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := funext h\nend Demo.M\n#print axioms Demo.M.no_ax\n#print axioms Demo.M.uses_choice\n#print axioms Demo.M.uses_funext\n";
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
