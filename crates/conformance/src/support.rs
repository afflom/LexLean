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
    let _guard = env_lock();
    let saved: Vec<(String, Option<String>)> = pairs
        .iter()
        .map(|(key, _)| ((*key).to_owned(), std::env::var(key).ok()))
        .collect();
    for (key, value) in pairs {
        match value {
            Some(value) => std::env::set_var(key, value),
            None => std::env::remove_var(key),
        }
    }
    let out = body();
    for (key, value) in saved {
        match value {
            Some(value) => std::env::set_var(&key, value),
            None => std::env::remove_var(&key),
        }
    }
    out
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

// ---- WS-B helpers ----
/// The proof-forms module: cases, right, induction, intro, structured apply
/// with a premise, and a one-step calculation, all Lean-verifiable.
pub const PROOF_FORMS_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{cases-goal}\n\\noaxioms\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\begin{proof}\n\\begin{cases}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nClose the goal by reflexivity.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m}\nClose the goal by reflexivity.\n\\end{case}\n\\end{cases}\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{right-goal}\n\\noaxioms\nFor every natural number \\(n\\), \\(n = 1\\) or \\(n + 0 = n\\).\n\\begin{proof}\nSelect the right alternative.\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{induction-goal}\n\\noaxioms\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\begin{proof}\n\\begin{induction}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nClose the goal by reflexivity.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m;ih}\nClose the goal by reflexivity.\n\\end{case}\n\\end{induction}\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{first}\n\\noaxioms\nIf \\(0 + 0 = 0\\), then \\(0 * 0 = 0\\).\n\\begin{proof}\nAssume \\(h\\).\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{apply-goal}\n\\noaxioms\n\\(0 * 0 = 0\\).\n\\begin{proof}\n\\begin{apply}{\\reference{Main::first}}\n\\begin{premise}{1}\nClose the goal by reflexivity.\n\\end{premise}\n\\end{apply}\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{zz}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{calc-goal}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\n\\begin{calculate}\n\\start{0 + 0}\n\\step{lexlean.core::eq}{0}{\\reference{Main::zz}}\n\\end{calculate}\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";

/// The exact generated Lean of [`PROOF_FORMS_MODULE`].
pub const PROOF_FORMS_LEAN: &str = "module\nimport Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic theorem cases_goal (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  cases llv0 with\n    | zero =>\n      rfl\n    | succ llh0 =>\n      rfl\n\npublic theorem right_goal (llv0 : Nat) : Or (Eq llv0 (1 : Nat)) (Eq (Nat.add llv0 0) llv0) := by\n  right\n  rfl\n\npublic theorem induction_goal (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  induction llv0 with\n    | zero =>\n      rfl\n    | succ llh0 llh1 =>\n      rfl\n\npublic theorem first : (Eq (Nat.add 0 0) (0 : Nat)) → Eq (Nat.mul 0 0) (0 : Nat) := by\n  intro llh0\n  rfl\n\npublic theorem apply_goal : Eq (Nat.mul 0 0) (0 : Nat) := by\n  apply LexLeanExample.Main.first\n  rfl\n\npublic theorem zz : Eq (Nat.add 0 0) (0 : Nat) := by\n  rfl\n\npublic theorem calc_goal : Eq (Nat.add 0 0) (0 : Nat) := by\n  calc (Nat.add 0 0) = (0 : Nat) := LexLeanExample.Main.zz\n\nend LexLeanExample.Main\n";

/// The exact canonical LaTeX body (after `\\begin{document}`) of
/// [`PROOF_FORMS_MODULE`].
pub const PROOF_FORMS_TEX_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}\n\\begin{theorem}\n\\label{ll:main:cases-goal}\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\end{theorem}\n\\begin{proof}\nConsider the cases of \\(n\\).\nCase zero:\nThe goal follows by reflexivity.\nCase \\(succ\\) with \\(m\\):\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:right-goal}\nFor every natural number \\(n\\), \\(n = 1\\) or \\(n + 0 = n\\).\n\\end{theorem}\n\\begin{proof}\nSelect the right alternative.\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:induction-goal}\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\end{theorem}\n\\begin{proof}\nProceed by induction on \\(n\\).\nCase zero:\nThe goal follows by reflexivity.\nCase \\(succ\\) with \\(m\\), \\(ih\\):\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:first}\nIf \\(0 + 0 = 0\\), then \\(0 \\cdot 0 = 0\\).\n\\end{theorem}\n\\begin{proof}\nAssume \\(h\\).\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:apply-goal}\n\\(0 \\cdot 0 = 0\\).\n\\end{theorem}\n\\begin{proof}\nApply \\(\\texttt{Main::first}\\).\nPremise \\(1\\):\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:zz}\n\\(0 + 0 = 0\\).\n\\end{theorem}\n\\begin{proof}\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:calc-goal}\n\\(0 + 0 = 0\\).\n\\end{theorem}\n\\begin{proof}\n\\begin{align*}\n0 + 0 &= 0 && \\text{by } \\texttt{Main::zz}\n\\end{align*}\n\\end{proof}\n\\end{document}\n";

/// A three-level section nest with two parameters of which one is used.
pub const SECTIONS_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{section}{outer}\n\\heading{Natural number addition}\n\\parameters{natural number \\(p\\); natural number \\(q\\)}\n\\begin{section}{middle}\n\\heading{Natural number addition}\n\\begin{section}{inner}\n\\heading{Natural number addition}\n\\begin{theorem}{deep}\n\\noaxioms\n\\(q + 0 = q\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{section}\n\\end{section}\n\\end{section}\n\\end{lexlean}\n";

/// The exact generated Lean of [`SECTIONS_MODULE`].
pub const SECTIONS_LEAN: &str = "module\nimport Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic theorem deep (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  rfl\n\nend LexLeanExample.Main\n";

/// The exact canonical LaTeX body of [`SECTIONS_MODULE`].
pub const SECTIONS_TEX_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}\n\\section{Natural number addition}\n\\label{ll:main:outer}\n\\[\\mathrm{Parameters}: \\forall p \\in \\mathbb{N}; \\forall q \\in \\mathbb{N}\\]\n\\subsection{Natural number addition}\n\\label{ll:main:middle}\n\\textbf{Natural number addition}\n\\label{ll:main:inner}\n\\begin{theorem}\n\\label{ll:main:deep}\n\\(q + 0 = q\\).\n\\end{theorem}\n\\begin{proof}\nThe goal follows by reflexivity.\n\\end{proof}\n\\end{document}\n";

/// The definitions fixture rendered exactly.
pub const DEFS_LEAN: &str = "module\nimport Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic def count : Type :=\n  Nat\n\npublic def double (llv0 : Nat) : Nat :=\n  Nat.add llv0 llv0\n\npublic def good : Prop :=\n  Exists (fun (llv0 : Nat) => Eq llv0 llv0)\n\npublic theorem add_zero (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  rfl\n\nend LexLeanExample.Main\n";

/// The exact canonical LaTeX body of [`DEFS_MODULE`].
pub const DEFS_TEX_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}\n\\begin{definition}\n\\label{ll:main:count}\nA count is defined as \\(\\mathbb{N}\\).\n\\end{definition}\n\\begin{definition}\n\\label{ll:main:double}\nFor every natural number \\(n\\), \\(\\operatorname{double}(n)\\) is defined as \\(n + n\\).\n\\end{definition}\n\\begin{definition}\n\\label{ll:main:good}\n\\(\\operatorname{good}\\) holds exactly when there exists a natural number \\(k\\) such that \\(k = k\\).\n\\end{definition}\n\\begin{theorem}\n\\label{ll:main:add-zero}\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\end{theorem}\n\\begin{proof}\nThe goal follows by reflexivity.\n\\end{proof}\n\\end{document}\n";

/// A unique-existence theorem over the `test.ext` fixture.
pub const UNIQUE_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.ext@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{unique}\n\\noaxioms\nThere exists exactly one natural number \\(k\\) such that \\(k = 0\\).\n\\begin{proof}\nUse \\(0\\) as the witness.\n\\begin{constructor}\n\\begin{branch}{1}\nClose the goal by reflexivity.\n\\end{branch}\n\\begin{branch}{2}\nAssume \\(y\\).\nAssume \\(h\\).\nClose the goal with \\(h\\).\n\\end{branch}\n\\end{constructor}\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";

/// The exact generated Lean of [`UNIQUE_MODULE`].
pub const UNIQUE_LEAN: &str = "module\nimport Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic theorem unique : Exists (fun (llv0 : Nat) => And (Eq llv0 (0 : Nat)) ((llv1 : Nat) → (Eq llv1 (0 : Nat)) → Eq llv1 llv0)) := by\n  refine ⟨(0 : Nat), ?_⟩\n  constructor\n  rfl\n  intro llh0\n  intro llh1\n  exact llh1\n\nend LexLeanExample.Main\n";

/// The exact canonical LaTeX body of [`UNIQUE_MODULE`].
pub const UNIQUE_TEX_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}\n\\begin{theorem}\n\\label{ll:main:unique}\nThere exists exactly one natural number \\(k\\) such that \\(k = 0\\).\n\\end{theorem}\n\\begin{proof}\nUse \\(0\\) as the witness.\nBranch \\(1\\):\nThe goal follows by reflexivity.\nBranch \\(2\\):\nAssume \\(y\\).\nAssume \\(h\\).\nThe goal follows from \\(h\\).\n\\end{proof}\n\\end{document}\n";

/// A defined value reaching Lean constants (`two`).
pub const DEFINED_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.ext@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{twoeq}\n\\noaxioms\n\\(two = two\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";

/// The exact generated Lean of [`DEFINED_MODULE`].
pub const DEFINED_LEAN: &str = "module\nimport Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic theorem twoeq : Eq (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero)) := by\n  rfl\n\nend LexLeanExample.Main\n";

/// LRE `sup`, `sub`, and `frac` renders.
pub const LRE_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.ext@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{sqhalf}\n\\noaxioms\nFor every natural number \\(n\\), \\(sq(n) = sq(n)\\) and \\(half(n) = half(n)\\).\n\\begin{proof}\n\\begin{constructor}\n\\begin{branch}{1}\nClose the goal by reflexivity.\n\\end{branch}\n\\begin{branch}{2}\nClose the goal by reflexivity.\n\\end{branch}\n\\end{constructor}\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";

/// The exact canonical LaTeX body of [`LRE_MODULE`].
pub const LRE_TEX_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}\n\\begin{theorem}\n\\label{ll:main:sqhalf}\nFor every natural number \\(n\\), \\({n}^{\\operatorname{two}} = {n}^{\\operatorname{two}}\\) and \\(\\frac{n}{{\\operatorname{h}}_{\\operatorname{i}}} = \\frac{n}{{\\operatorname{h}}_{\\operatorname{i}}}\\).\n\\end{theorem}\n\\begin{proof}\nBranch \\(1\\):\nThe goal follows by reflexivity.\nBranch \\(2\\):\nThe goal follows by reflexivity.\n\\end{proof}\n\\end{document}\n";

/// A section parameter whose type depends on an earlier parameter.
pub const DEPENDENT_MODULE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.ext@1.0.0}\n\\title{Natural number addition}\n\n\\begin{section}{outer}\n\\heading{Natural number addition}\n\\parameters{natural number \\(n\\); \\(fin(n)\\) \\(i\\)}\n\\begin{theorem}{dep}\n\\noaxioms\n\\(i = i\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{section}\n\\end{lexlean}\n";

/// The exact generated Lean of [`DEPENDENT_MODULE`].
pub const DEPENDENT_LEAN: &str = "module\nimport Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic theorem dep (llv0 : Nat) (llv1 : Fin llv0) : Eq llv1 llv1 := by\n  rfl\n\nend LexLeanExample.Main\n";

/// The `test.ext` fixture entries: a universe-polymorphic proof constant
/// (`Eq.symm`), a numeral-bearing signature (`Nat.zero_add`), a defined
/// value reaching Lean constants, LRE sup/sub/frac renders, and a dependent
/// type function (`Fin`).
#[must_use]
pub fn ext_entries() -> Vec<(&'static str, &'static str)> {
    vec![
        ("eqsymm.toml", "spec = \"lexlean/entry/1\"\nid = \"eqsymm\"\ncategory = \"proof-constant\"\nsignature = \"(pi ((implicit a (sort (type u))) (implicit x (local a)) (implicit y (local a)) (explicit h (app (const lexlean.core::eq) (local a) (local x) (local y)))) (app (const lexlean.core::eq) (local a) (local y) (local x)))\"\nuniverses = [\"u\"]\nsurface_arity = 1\nframe = \"call\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Eq.symm\"\n\n[[form]]\nid = \"eqsymm\"\nchannel = \"math\"\nsurface = \"eqsymm\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(seq (operator-name eqsymm) (paren (slot 0)))\"\n"),
        ("fin.toml", "spec = \"lexlean/entry/1\"\nid = \"fin\"\ncategory = \"function\"\nsignature = \"(pi ((explicit n (const lexlean.std.nat::nat))) (sort (type 0)))\"\nsurface_arity = 1\nframe = \"call\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Fin\"\n\n[[form]]\nid = \"fin\"\nchannel = \"math\"\nsurface = \"fin\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(seq (operator-name fin) (paren (slot 0)))\"\n"),
        ("half.toml", "spec = \"lexlean/entry/1\"\nid = \"half\"\ncategory = \"function\"\nsignature = \"(pi ((explicit n (const lexlean.std.nat::nat))) (const lexlean.std.nat::nat))\"\nsurface_arity = 1\nframe = \"call\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Nat.pred\"\n\n[[form]]\nid = \"half\"\nchannel = \"math\"\nsurface = \"half\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(frac (slot 0) (sub (operator-name h) (operator-name i)))\"\n"),
        ("sq.toml", "spec = \"lexlean/entry/1\"\nid = \"sq\"\ncategory = \"function\"\nsignature = \"(pi ((explicit n (const lexlean.std.nat::nat))) (const lexlean.std.nat::nat))\"\nsurface_arity = 1\nframe = \"call\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Nat.succ\"\n\n[[form]]\nid = \"sq\"\nchannel = \"math\"\nsurface = \"sq\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(sup (slot 0) (operator-name two))\"\n"),
        ("two.toml", "spec = \"lexlean/entry/1\"\nid = \"two\"\ncategory = \"term-constant\"\nsignature = \"(const lexlean.std.nat::nat)\"\nsurface_arity = 0\nframe = \"atom\"\n\n[denotation]\nkind = \"defined\"\nvalue = \"(app (const lexlean.std.nat::succ) (app (const lexlean.std.nat::succ) (const lexlean.std.nat::zero)))\"\n\n[[form]]\nid = \"two\"\nchannel = \"both\"\nsurface = \"two\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(operator-name two)\"\n"),
        ("zeroadd.toml", "spec = \"lexlean/entry/1\"\nid = \"zeroadd\"\ncategory = \"proof-constant\"\nsignature = \"(pi ((explicit n (const lexlean.std.nat::nat))) (app (const lexlean.core::eq) (const lexlean.std.nat::nat) (app (const lexlean.std.nat::add) (nat 0) (local n)) (local n)))\"\nsurface_arity = 1\nframe = \"call\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Nat.zero_add\"\n\n[[form]]\nid = \"zeroadd\"\nchannel = \"math\"\nsurface = \"zeroadd\"\ncanonical_source = true\nfeatures = []\n\n[render]\nmath = \"(seq (operator-name zeroadd) (paren (slot 0)))\"\n"),
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
