//! Property tests (SPEC.md §28.1 class 2): normalization, canonical
//! serialization, alpha-safe scope handling, and formatter idempotence.

use proptest::prelude::*;

use lexlean::artifact::canonical_json::Json;
use lexlean::ir::term::{Binder, LocalId, Renumber, Term};
use lexlean::lexicon::lse::BinderMode;
use lexlean::source::normalize::normalize;

/// Lines of printable ASCII with no percent, tab, or trailing space: the
/// alphabet normalization accepts unchanged.
fn clean_line() -> impl Strategy<Value = String> {
    proptest::collection::vec(
        proptest::char::range('a', 'z').prop_union(proptest::char::range('A', 'Z')),
        0..24,
    )
    .prop_map(|chars| chars.into_iter().collect())
}

proptest! {
    /// §12.1: normalization is idempotent on its own output.
    #[test]
    fn normalization_is_idempotent(lines in proptest::collection::vec(clean_line(), 1..8)) {
        prop_assume!(lines.last().is_some_and(|line| !line.is_empty()));
        let text = format!("{}\n", lines.join("\n"));
        let once = normalize("m", text.as_bytes(), true).expect("accepts clean input");
        let twice = normalize("m", once.text.as_bytes(), true).expect("accepts its own output");
        prop_assert_eq!(once.text, twice.text);
    }

    /// §12.1: fmt-mode normalization always yields NFC with one final LF.
    #[test]
    fn normalization_output_is_canonical(lines in proptest::collection::vec(clean_line(), 1..8)) {
        prop_assume!(lines.last().is_some_and(|line| !line.is_empty()));
        let text = format!("{}\n", lines.join("\n"));
        let normalized = normalize("m", text.as_bytes(), true).expect("accepts clean input");
        prop_assert!(normalized.text.ends_with('\n'));
        prop_assert!(!normalized.text.contains('\r'));
        prop_assert!(unicode_normalization::is_nfc(&normalized.text));
    }

    /// §21.7: canonical serialization is a parse/print fixpoint.
    #[test]
    fn canonical_json_roundtrips(
        keys in proptest::collection::btree_set("[a-z]{1,6}", 1..6),
        values in proptest::collection::vec(0u64..1_000_000, 6),
    ) {
        let object = Json::Obj(
            keys.iter()
                .cloned()
                .zip(values.iter().map(|value| {
                    Json::from_usize(usize::try_from(*value).expect("small"))
                }))
                .collect(),
        );
        let printed = object.to_canonical_string();
        let reparsed = Json::parse(printed.as_bytes()).expect("own output parses");
        prop_assert_eq!(reparsed.to_canonical_string(), printed);
    }

    /// §17.9: the canonical key ignores both spellings and the numeric
    /// identity of locals; only binding structure matters.
    #[test]
    fn canonical_key_is_alpha_safe(
        id_a in 0u64..1_000, id_b in 1_000u64..2_000,
        name_a in "[a-z]{1,4}", name_b in "[a-z]{1,4}",
    ) {
        let build = |id: u64, spelling: &str| Term::Pi {
            binders: vec![Binder {
                id: LocalId(id),
                mode: BinderMode::Explicit,
                ty: lexlean::ir::term::prop(),
                spelling: spelling.to_owned(),
            }],
            body: Box::new(Term::Local(LocalId(id))),
        };
        prop_assert_eq!(
            build(id_a, &name_a).canonical_key(),
            build(id_b, &name_b).canonical_key()
        );
    }

    /// §17.9: serialization with a fresh renumberer is deterministic.
    #[test]
    fn renumbering_is_deterministic(id in 0u64..10_000) {
        let term = Term::Pi {
            binders: vec![Binder {
                id: LocalId(id),
                mode: BinderMode::Explicit,
                ty: lexlean::ir::term::prop(),
                spelling: "x".to_owned(),
            }],
            body: Box::new(Term::Local(LocalId(id))),
        };
        let first = term.to_json(&mut Renumber::default()).to_canonical_string();
        let second = term.to_json(&mut Renumber::default()).to_canonical_string();
        prop_assert_eq!(first, second);
    }
}

/// §23.5: the formatter is idempotent over legal whitespace variance of the
/// literal example (fmt then fmt changes nothing).
#[test]
fn formatter_is_idempotent_on_the_example() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("repo root")
        .to_path_buf();
    let source = std::fs::read_to_string(root.join("examples/nat-add-zero/src/Main.lex.tex"))
        .expect("example source");
    for padded in [
        source.clone(),
        source.replace("\n\\begin{theorem}", "\n\n\n\\begin{theorem}"),
    ] {
        let temp = tempfile::tempdir().expect("tempdir");
        for entry in walkdir::WalkDir::new(root.join("examples/nat-add-zero"))
            .into_iter()
            .flatten()
        {
            let relative = entry
                .path()
                .strip_prefix(root.join("examples/nat-add-zero"))
                .expect("under example");
            let text = relative.to_string_lossy();
            if text.is_empty() || text.starts_with(".lexlean") || text.starts_with("expected") {
                continue;
            }
            let destination = temp.path().join(relative);
            if entry.file_type().is_dir() {
                std::fs::create_dir_all(&destination).expect("mkdir");
            } else {
                if let Some(parent) = destination.parent() {
                    std::fs::create_dir_all(parent).expect("mkdir");
                }
                std::fs::copy(entry.path(), &destination).expect("copy");
            }
        }
        std::fs::write(temp.path().join("src/Main.lex.tex"), &padded).expect("write");
        let config =
            camino::Utf8PathBuf::from_path_buf(temp.path().join("lexlean.toml")).expect("utf8");
        let engine = lexlean::Engine::load(&config).expect("loads");
        engine
            .format(lexlean::FormatRequest {
                selection: lexlean::Selection::Entrypoints,
                check_only: false,
            })
            .expect("first format");
        let after_one =
            std::fs::read_to_string(temp.path().join("src/Main.lex.tex")).expect("read");
        engine
            .format(lexlean::FormatRequest {
                selection: lexlean::Selection::Entrypoints,
                check_only: false,
            })
            .expect("second format");
        let after_two =
            std::fs::read_to_string(temp.path().join("src/Main.lex.tex")).expect("read");
        assert_eq!(after_one, after_two, "fmt is idempotent");
        assert_eq!(after_one, source, "fmt reaches the canonical bytes");
    }
}
