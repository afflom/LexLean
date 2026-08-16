//! Unit tests (SPEC.md §28.1 class 1): scanners, parsers, LSE/LRE, IR,
//! hashing, path rules, and output parsers, each against its §-oracle.

use lexlean::artifact::canonical_json::Json;
use lexlean::artifact::content_id::{FramedHasher, Sha256Digest};
use lexlean::ir::term::{Binder, LocalId, Term};
use lexlean::lexicon::lse;
use lexlean::source::atom::AtomClass;
use lexlean::source::scan::scan;

/// §12.2: the scanner recognizes exactly the atom classes with exact spans.
#[test]
fn scanner_atom_classes_and_spans() {
    let text = "\\begin{x} word 42 + \u{2115}\n";
    let atoms = scan("m", text, 1_000).expect("scan");
    let observed: Vec<(AtomClass, &str)> = atoms
        .iter()
        .map(|atom| (atom.class, &text[atom.byte_start..atom.byte_end]))
        .collect();
    assert_eq!(
        observed,
        vec![
            (AtomClass::Control, "\\begin"),
            (AtomClass::Delimiter, "{"),
            (AtomClass::Word, "x"),
            (AtomClass::Delimiter, "}"),
            (AtomClass::Whitespace, " "),
            (AtomClass::Word, "word"),
            (AtomClass::Whitespace, " "),
            (AtomClass::Numeral, "42"),
            (AtomClass::Whitespace, " "),
            (AtomClass::AsciiSymbol, "+"),
            (AtomClass::Whitespace, " "),
            (AtomClass::UnicodeSymbol, "\u{2115}"),
            (AtomClass::Whitespace, "\n"),
        ]
    );
}

/// §12.2: an atom-count limit is a checked limit, not an allocation.
#[test]
fn scanner_enforces_the_atom_limit() {
    let error = scan("m", "a b c d e", 3).expect_err("limited");
    assert_eq!(error.code.as_str(), "LLS8002");
}

/// §13.8: LSE parses and reprints its own canonical form.
#[test]
fn lse_roundtrips_canonically() {
    let text = "(pi ((explicit n (const lexlean.std.nat::nat))) (app (const lexlean.core::eq (0)) (const lexlean.std.nat::nat) (local n) (local n)))";
    let parsed = lse::parse(text, 64).expect("parses");
    let printed = parsed.print(false);
    let reparsed = lse::parse(&printed, 64).expect("reparses");
    assert_eq!(reparsed.print(false), printed, "printing is a fixpoint");
}

/// §13.8: unbound locals are rejected at scope checking.
#[test]
fn lse_rejects_unbound_locals() {
    let parsed = lse::parse("(local ghost)", 64).expect("parses structurally");
    assert!(
        parsed
            .check_scopes(&std::collections::BTreeSet::new())
            .is_err(),
        "an unbound local fails scope checking"
    );
}

/// §21.1: the frame function has the exact byte layout.
#[test]
fn frame_layout_is_exact() {
    use sha2::Digest;
    let mut framed = FramedHasher::new("d");
    framed.frame("label", b"body");
    let mut manual = sha2::Sha256::new();
    manual.update(b"d\0");
    manual.update(5u32.to_be_bytes());
    manual.update(b"label");
    manual.update(4u64.to_be_bytes());
    manual.update(b"body");
    let digest: [u8; 32] = manual.finalize().into();
    assert_eq!(framed.finish(), Sha256Digest(digest));
}

/// §21.7: canonical JSON sorts keys, refuses floats and null, and
/// distinguishes the hash form from the file form by exactly one LF.
#[test]
fn canonical_json_is_restricted() {
    assert!(Json::parse(b"3.14").is_err());
    assert!(Json::parse(b"null").is_err());
    let object = Json::object(vec![("b", Json::from_usize(2)), ("a", Json::from_usize(1))]);
    assert_eq!(object.to_canonical_string(), "{\"a\":1,\"b\":2}");
    assert_eq!(object.to_file_bytes(), b"{\"a\":1,\"b\":2}\n");
}

/// §17.9: the canonical key is alpha-safe --- spelling changes nothing.
#[test]
fn canonical_key_is_alpha_safe() {
    let with = |spelling: &str, id: u64| Term::Pi {
        binders: vec![Binder {
            id: LocalId(id),
            mode: lexlean::lexicon::lse::BinderMode::Explicit,
            ty: lexlean::ir::term::prop(),
            spelling: spelling.to_owned(),
        }],
        body: Box::new(Term::Local(LocalId(id))),
    };
    assert_eq!(
        with("n", 3).canonical_key(),
        with("m", 77).canonical_key(),
        "alpha-renamed terms share one canonical key"
    );
}

/// §10.1: the project-relative path rule.
#[test]
fn path_rules_are_strict() {
    use lexlean::config::is_project_relative;
    assert!(is_project_relative("src/Main.lex.tex"));
    assert!(!is_project_relative("/etc/passwd"));
    assert!(!is_project_relative("../escape"));
    assert!(!is_project_relative("a/../../b"));
    assert!(!is_project_relative(""));
}

/// §22.5: the axiom-output parser accepts and rejects the committed golden
/// vectors, line by line.
#[test]
fn axiom_parser_matches_the_golden_vectors() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("repo root")
        .to_path_buf();
    let name_of = |line: &str| {
        line.split('\'')
            .nth(1)
            .unwrap_or("Demo.M.unknown")
            .to_owned()
    };
    let accepted =
        std::fs::read_to_string(root.join("tests/golden/axiom-parser/accepted.txt")).expect("read");
    for line in accepted.lines().filter(|line| !line.trim().is_empty()) {
        lexlean::verify::axiom::parse_audit_output(line, &[name_of(line)])
            .unwrap_or_else(|error| panic!("accepted vector rejected: {line}: {error:?}"));
    }
    let rejected =
        std::fs::read_to_string(root.join("tests/golden/axiom-parser/rejected.txt")).expect("read");
    for line in rejected.lines().filter(|line| !line.trim().is_empty()) {
        assert!(
            lexlean::verify::axiom::parse_audit_output(line, &[name_of(line)]).is_err(),
            "rejected vector accepted: {line}"
        );
    }
}

/// §22.7: process normalization replaces every pinned prefix and
/// normalizes line endings and blank tails.
#[test]
fn process_normalization_is_exact() {
    let normalizer = lexlean::verify::child::Normalizer::new(
        camino::Utf8Path::new("/stage"),
        camino::Utf8Path::new("/proj"),
        camino::Utf8Path::new("/proj/lake"),
        camino::Utf8Path::new("/tool"),
    );
    let normalized = normalizer.normalize(b"/stage/x\r\n/proj/y ok\n/tool/bin z\n\n\n");
    assert_eq!(normalized, "$STAGING/x\n$PROJECT/y ok\n$TOOLCHAIN/bin z\n");
}

/// §22.7: after prefix replacement, any remaining rooted path is
/// unexpected; placeholders and URL schemes are not paths.
#[test]
fn unexpected_absolute_path_detector_is_exact() {
    use lexlean::verify::child::first_unexpected_absolute_path as detect;
    for clean in [
        "",
        "ok\n",
        "$STAGING/x $PROJECT/y $TOOLCHAIN/bin $HOME/z $LAKE_WORKSPACE/w",
        "see https://example.invalid/path and file://host/x",
        "ratio 1/2 and a / b and /- comment -/",
        "'Foo.bar' depends on axioms: [propext]",
        "the C: drive is not a path without a separator",
        "x=$STAGING/y,$PROJECT/z",
    ] {
        assert_eq!(detect(clean), None, "{clean:?} is clean");
    }
    for (dirty, token) in [
        ("/home/user/x", "/home/user/x"),
        (
            "error at /tmp/lexlean-abc/y.lean:1:2",
            "/tmp/lexlean-abc/y.lean:1:2",
        ),
        ("path \"/workspaces/lex/a\" here", "/workspaces/lex/a"),
        ("(/Users/me/z)", "/Users/me/z"),
        ("[/var/lib]", "/var/lib"),
        ("C:\\Users\\me\\x", "C:\\Users\\me\\x"),
        ("at D:/work/y.lean", "D:/work/y.lean"),
        ("x=/opt/lean", "/opt/lean"),
        ("/.hidden", "/.hidden"),
        ("/_x", "/_x"),
    ] {
        let found = detect(dirty).unwrap_or_else(|| panic!("{dirty:?} is dirty"));
        assert_eq!(found.1, token, "{dirty:?}");
    }
    let normalizer = lexlean::verify::child::Normalizer::new(
        camino::Utf8Path::new("/stage"),
        camino::Utf8Path::new("/proj"),
        camino::Utf8Path::new("/proj/lake"),
        camino::Utf8Path::new("/tool"),
    );
    assert!(!normalizer.has_unexpected_absolute_path("$STAGING/a\n"));
    assert!(normalizer.has_unexpected_absolute_path("$STAGING/a /elsewhere/b\n"));
}

/// §8.3, §24.5: a non-UTF-8 argument or working directory is the
/// registered environment diagnostic (exit 3), never a panic, in both
/// output modes.
#[cfg(unix)]
#[test]
fn non_utf8_argv_and_cwd_are_environment_diagnostics() {
    use std::os::unix::ffi::OsStrExt;
    let binary = env!("CARGO_BIN_EXE_lexlean");
    let bad = std::ffi::OsStr::from_bytes(b"src/Bad\xff.lex.tex");
    let output = std::process::Command::new(binary)
        .args(["--color", "never", "check"])
        .arg(bad)
        .output()
        .expect("runs");
    assert_eq!(output.status.code(), Some(3), "environment class");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.starts_with("error[LLV7008]"), "{stderr}");
    assert!(output.stdout.is_empty());
    let output = std::process::Command::new(binary)
        .args(["--diagnostic-format", "json", "check"])
        .arg(bad)
        .output()
        .expect("runs");
    assert_eq!(output.status.code(), Some(3));
    assert!(output.stderr.is_empty(), "JSON mode keeps stderr empty");
    let value: serde_json::Value = serde_json::from_slice(&output.stdout).expect("json");
    assert_eq!(value["command"], "check");
    assert_eq!(value["exit_code"], 3);
    assert_eq!(value["diagnostics"][0]["code"], "LLV7008");

    let temp = tempfile::tempdir().expect("tempdir");
    let bad_dir = temp.path().join(std::ffi::OsStr::from_bytes(b"cwd\xff"));
    std::fs::create_dir(&bad_dir).expect("mkdir");
    let output = std::process::Command::new(binary)
        .args(["--color", "never", "check"])
        .current_dir(&bad_dir)
        .output()
        .expect("runs");
    assert_eq!(
        output.status.code(),
        Some(3),
        "a non-UTF-8 cwd is an environment failure"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.starts_with("error[LLV7008]"), "{stderr}");
}
