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
category = "type-noun"
signature = "(pi ((explicit p (sort prop)) (explicit q (sort prop))) (sort prop))"
surface_arity = 0
frame = "atom"

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
math = "(operator-name {id})"

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
For every natural number \(a\) and natural number \(b\), \(succ(a) + combine((b + 0), a) = combine(b, a) + succ(a)\).
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
                || line.starts_with(&format!("public def {lean_name} "))
        })
        .unwrap_or_else(|| panic!("`{lean_name}` in the corpus Lean:\n{lean}"));
    let end = lines[start + 1..]
        .iter()
        .position(|line| line.starts_with("public ") || line.starts_with("end "))
        .map_or(lines.len(), |offset| start + 1 + offset);
    let mut block = lines[start..end].join("\n");
    while block.ends_with('\n') {
        block.pop();
    }
    block.trim_end().to_owned()
}
