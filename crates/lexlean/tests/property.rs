//! Property tests (SPEC.md §28.1 class 2): normalization over the real
//! source alphabet, canonical serialization over structured values,
//! alpha-safe scope handling over generated binder terms, and formatter
//! idempotence over every example.

use std::collections::BTreeMap;

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

/// One piece of the real `.lex.tex` alphabet (§12.1, §12.2): controls,
/// braces, math delimiters, ASCII and Unicode symbols, words, numerals,
/// letters in NFC and in NFD (`e` + combining acute), and every line
/// ending, plus the forbidden scalars normalization must report: tab,
/// no-break space, and the raw percent.
fn source_piece() -> impl Strategy<Value = &'static str> {
    prop_oneof![
        8 => Just("word"),
        4 => Just(" "),
        3 => Just("\\begin{theorem}{add-zero}"),
        3 => Just("\\(n + 0 = n\\)"),
        2 => Just("ℕ"),
        2 => Just("é"),
        2 => Just("e\u{0301}"),
        2 => Just("42"),
        2 => Just("\u{00E5}\u{0308}"),
        6 => Just("\n"),
        3 => Just("\r\n"),
        2 => Just("\r"),
        1 => Just("\t"),
        1 => Just("\u{00A0}"),
        1 => Just("%"),
    ]
}

/// A source text over [`source_piece`]: an arbitrary mix, so most inputs
/// exercise several normalization rules at once.
fn source_text() -> impl Strategy<Value = String> {
    proptest::collection::vec(source_piece(), 0..40).prop_map(|pieces| pieces.concat())
}

/// The line-ending normalization §12.1 prescribes, spelled independently
/// of the implementation.
fn lf_only(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}

/// A canonical JSON value of bounded depth over every variant: booleans,
/// the full `i64` range, strings needing escapes (quotes, backslashes,
/// control scalars, non-ASCII), arrays, and objects with such keys.
fn json_value() -> impl Strategy<Value = Json> {
    let leaf = prop_oneof![
        any::<bool>().prop_map(Json::Bool),
        any::<i64>().prop_map(Json::Int),
        json_string().prop_map(Json::Str),
    ];
    leaf.prop_recursive(4, 48, 6, |inner| {
        prop_oneof![
            proptest::collection::vec(inner.clone(), 0..6).prop_map(Json::Arr),
            proptest::collection::btree_map(json_string(), inner, 0..6).prop_map(Json::Obj),
        ]
    })
}

fn json_string() -> impl Strategy<Value = String> {
    proptest::collection::vec(
        prop_oneof![
            6 => proptest::char::range('a', 'z'),
            1 => Just('"'),
            1 => Just('\\'),
            1 => Just('\n'),
            1 => Just('\u{0001}'),
            1 => Just('\u{007F}'),
            1 => Just('é'),
            1 => Just('ℕ'),
            1 => Just('\u{1F600}'),
        ],
        0..8,
    )
    .prop_map(|chars| chars.into_iter().collect())
}

/// A shape for a closed binder term: `Pi`/`Lambda` nodes over locals bound
/// by enclosing binders (De Bruijn levels), applications, and the sort
/// `Prop` as every binder type or leaf.
#[derive(Debug, Clone)]
enum Shape {
    Prop,
    Bound(usize),
    Pi(Box<Shape>),
    Lambda(Box<Shape>),
    App(Box<Shape>, Box<Shape>),
}

fn shape() -> impl Strategy<Value = Shape> {
    let leaf = prop_oneof![Just(Shape::Prop), (0usize..8).prop_map(Shape::Bound)];
    leaf.prop_recursive(6, 32, 2, |inner| {
        prop_oneof![
            inner.clone().prop_map(|body| Shape::Pi(Box::new(body))),
            inner.clone().prop_map(|body| Shape::Lambda(Box::new(body))),
            (inner.clone(), inner).prop_map(|(f, a)| Shape::App(Box::new(f), Box::new(a))),
        ]
    })
}

/// Realize a shape as a closed term: binder `k` (counting from the
/// outside) gets `LocalId(base + k)` and the spelling `prefix{k}`; a
/// `Bound(i)` under fewer than `i + 1` binders refers to the outermost
/// one, so every realized term is closed.
fn realize(shape: &Shape, base: u64, prefix: &str, depth: usize) -> Term {
    match shape {
        Shape::Prop => lexlean::ir::term::prop(),
        Shape::Bound(level) => {
            if depth == 0 {
                lexlean::ir::term::prop()
            } else {
                let level = (*level).min(depth - 1);
                Term::Local(LocalId(base + u64::try_from(level).expect("small")))
            }
        }
        Shape::Pi(body) | Shape::Lambda(body) => {
            let binder = Binder {
                id: LocalId(base + u64::try_from(depth).expect("small")),
                mode: BinderMode::Explicit,
                ty: lexlean::ir::term::prop(),
                spelling: format!("{prefix}{depth}"),
            };
            let body = Box::new(realize(body, base, prefix, depth + 1));
            if matches!(shape, Shape::Pi(_)) {
                Term::Pi {
                    binders: vec![binder],
                    body,
                }
            } else {
                Term::Lambda {
                    binders: vec![binder],
                    body,
                }
            }
        }
        Shape::App(function, argument) => Term::App {
            function: Box::new(realize(function, base, prefix, depth)),
            explicit_args: vec![realize(argument, base, prefix, depth)],
            omitted_implicit_binders: Vec::new(),
        },
    }
}

fn shape_has_binder(shape: &Shape) -> bool {
    match shape {
        Shape::Prop | Shape::Bound(_) => false,
        Shape::Pi(_) | Shape::Lambda(_) => true,
        Shape::App(function, argument) => shape_has_binder(function) || shape_has_binder(argument),
    }
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

    /// §12.1 over the real alphabet: normalization is a pure function of
    /// its input (the same bytes give the same text or the same
    /// diagnostics, spans included), and CRLF, CR, and LF are one line
    /// ending — every outcome, including every diagnostic span, is
    /// identical to the outcome on the LF-only spelling of the same text.
    #[test]
    fn normalization_is_deterministic_and_line_ending_blind(text in source_text()) {
        for for_fmt in [false, true] {
            let first = normalize("m", text.as_bytes(), for_fmt);
            let second = normalize("m", text.as_bytes(), for_fmt);
            prop_assert_eq!(&first, &second, "deterministic (fmt = {})", for_fmt);
            let lf = lf_only(&text);
            let on_lf = normalize("m", lf.as_bytes(), for_fmt);
            prop_assert_eq!(&first, &on_lf, "line endings are one (fmt = {})", for_fmt);
        }
    }

    /// §12.1: whatever fmt-mode normalization accepts is canonical (NFC,
    /// LF only, exactly one final LF, no forbidden scalar) and is a
    /// fixpoint of both modes.
    #[test]
    fn accepted_source_is_a_fixpoint_of_both_modes(text in source_text()) {
        if let Ok(once) = normalize("m", text.as_bytes(), true) {
            prop_assert!(unicode_normalization::is_nfc(&once.text));
            prop_assert!(!once.text.contains('\r'));
            prop_assert!(once.text.ends_with('\n') && !once.text.ends_with("\n\n"));
            for forbidden in ['\t', '\u{00A0}', '%'] {
                prop_assert!(!once.text.contains(forbidden));
            }
            let strict = normalize("m", once.text.as_bytes(), false).expect("strict accepts canonical text");
            let again = normalize("m", once.text.as_bytes(), true).expect("fmt accepts canonical text");
            prop_assert_eq!(&strict.text, &once.text);
            prop_assert_eq!(&again.text, &once.text);
        }
    }

    /// §12.1: every tab, no-break space, and raw percent is reported, each
    /// with its own registered code and one diagnostic per occurrence; a
    /// non-NFC text is rejected in strict mode (`LLL1003`) and rewritten
    /// to NFC in fmt mode, to exactly what the pre-composed text gives.
    #[test]
    fn forbidden_scalars_and_nfd_are_reported_exactly(text in source_text()) {
        let lf = lf_only(&text);
        let tabs = lf.matches('\t').count();
        let nbsps = lf.matches('\u{00A0}').count();
        let percents = lf.matches('%').count();
        let is_nfc = unicode_normalization::is_nfc(&lf);
        match normalize("m", text.as_bytes(), false) {
            Ok(_) => {
                prop_assert_eq!((tabs, nbsps, percents), (0, 0, 0));
                prop_assert!(is_nfc);
            }
            Err(diagnostics) => {
                if !is_nfc {
                    // NFC is checked before the scalar walk: the sole
                    // diagnostic is the NFC rejection.
                    prop_assert_eq!(diagnostics.len(), 1);
                    prop_assert_eq!(diagnostics[0].code.as_str(), "LLL1003");
                    prop_assert_eq!(&diagnostics[0].message, "source is not Unicode NFC");
                } else {
                    let count = |code: &str, message: &str| {
                        diagnostics
                            .iter()
                            .filter(|d| d.code.as_str() == code && d.message == message)
                            .count()
                    };
                    prop_assert_eq!(count("LLL1002", "tab is forbidden"), tabs);
                    prop_assert_eq!(count("LLL1001", "non-ASCII whitespace U+00A0 is forbidden"), nbsps);
                    prop_assert_eq!(
                        count("LLL1002", "a raw percent character is forbidden; TeX comments do not exist"),
                        percents
                    );
                }
            }
        }
        if !is_nfc {
            use unicode_normalization::UnicodeNormalization;
            let composed: String = lf.nfc().collect();
            let from_nfd = normalize("m", text.as_bytes(), true);
            let from_nfc = normalize("m", composed.as_bytes(), true);
            prop_assert_eq!(from_nfd, from_nfc, "fmt mode composes to NFC first");
        }
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

    /// §21.7 over structured values: nested arrays and objects, the full
    /// integer range, and strings needing escapes round-trip to the same
    /// value and the same bytes; the file form is the payload plus one LF.
    #[test]
    fn canonical_json_roundtrips_structured_values(value in json_value()) {
        let printed = value.to_canonical_string();
        let reparsed = Json::parse(printed.as_bytes()).expect("own output parses");
        prop_assert_eq!(&reparsed, &value, "the value survives");
        prop_assert_eq!(reparsed.to_canonical_string(), printed.clone(), "the bytes survive");
        // Control scalars are escaped: the payload is one line with no
        // raw control character.
        prop_assert!(!printed.chars().any(|c| (c as u32) < 0x20), "{printed}");
        let file = value.to_file_bytes();
        prop_assert_eq!(&file[..file.len() - 1], printed.as_bytes());
        prop_assert_eq!(file.last(), Some(&b'\n'));
        prop_assert!(!printed.ends_with('\n'));
        // A parsed object keeps every key exactly once.
        if let Json::Obj(map) = &value {
            let Json::Obj(back) = &reparsed else {
                return Err(TestCaseError::fail("an object reparses as an object"));
            };
            prop_assert_eq!(map.keys().collect::<Vec<_>>(), back.keys().collect::<Vec<_>>());
        }
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

    /// §17.9 over generated `Pi`/`Lambda`/`App` terms: two alpha-variants
    /// of one closed shape (every binder identity and spelling changed
    /// consistently) share the canonical key, the comparison key, and the
    /// renumbered serialization; a shape with a binder differs from the
    /// same shape with that binder's kind flipped, so the key sees
    /// structure and nothing else.
    #[test]
    fn binder_serialization_is_alpha_safe_over_generated_terms(
        shape in shape(),
        base_a in 0u64..1_000, base_b in 10_000u64..20_000,
        prefix_a in "[a-z]{1,3}", prefix_b in "[A-Z]{1,3}",
    ) {
        let a = realize(&shape, base_a, &prefix_a, 0);
        let b = realize(&shape, base_b, &prefix_b, 0);
        prop_assert_eq!(a.canonical_key(), b.canonical_key(), "alpha-variants share the canonical key");
        prop_assert_eq!(a.eq_key(), b.eq_key(), "closed alpha-variants share the comparison key");
        // The renumbered serialization keeps display spellings (metadata)
        // but never a raw local identity: every `id` is a dense index.
        let serialized_b = b.to_json(&mut Renumber::default()).to_canonical_string();
        prop_assert!(
            !serialized_b.contains(&format!("\"id\":{base_b}")),
            "dense renumbering, not the raw identity: {serialized_b}"
        );
        prop_assert_eq!(
            serialized_b.replace(&prefix_b, &prefix_a),
            a.to_json(&mut Renumber::default()).to_canonical_string(),
            "alpha-variants differ in spellings alone"
        );
        prop_assert_eq!(
            a.to_json(&mut Renumber::default()).to_canonical_string(),
            a.to_json(&mut Renumber::default()).to_canonical_string(),
            "a fresh renumberer is deterministic"
        );
        if shape_has_binder(&shape) {
            fn flip(shape: &Shape) -> Shape {
                match shape {
                    Shape::Pi(body) => Shape::Lambda(body.clone()),
                    Shape::Lambda(body) => Shape::Pi(body.clone()),
                    Shape::App(function, argument) => {
                        if shape_has_binder(function) {
                            Shape::App(Box::new(flip(function)), argument.clone())
                        } else {
                            Shape::App(function.clone(), Box::new(flip(argument)))
                        }
                    }
                    other => other.clone(),
                }
            }
            let flipped = realize(&flip(&shape), base_a, &prefix_a, 0);
            prop_assert_ne!(a.canonical_key(), flipped.canonical_key(), "structure is visible");
        }
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

/// The repository root, when the crate is being tested inside it.
///
/// `examples/` is repository data, not crate data, and `cargo package`
/// cannot reach outside the package. Inside the repository the directory is
/// always found, so nothing is skipped where the gate runs.
fn repo_root() -> Option<std::path::PathBuf> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)?
        .to_path_buf();
    if root.join("examples/nat-add-zero/lexlean.toml").is_file() {
        return Some(root);
    }
    eprintln!(
        "the crate is being tested outside its repository; the assertions that read examples/ did not run"
    );
    None
}

/// Copy one example (without its build root and oracles) into a fresh
/// temporary directory.
fn copy_example(example: &std::path::Path, temp: &std::path::Path) {
    for entry in walkdir::WalkDir::new(example).into_iter().flatten() {
        let relative = entry.path().strip_prefix(example).expect("under example");
        let text = relative.to_string_lossy();
        if text.is_empty() || text.starts_with(".lexlean") || text.starts_with("expected") {
            continue;
        }
        let destination = temp.join(relative);
        if entry.file_type().is_dir() {
            std::fs::create_dir_all(&destination).expect("mkdir");
        } else {
            if let Some(parent) = destination.parent() {
                std::fs::create_dir_all(parent).expect("mkdir");
            }
            std::fs::copy(entry.path(), &destination).expect("copy");
        }
    }
}

/// Every `.lex.tex` module of an example, relative to the example root,
/// with its committed source.
fn example_modules(example: &std::path::Path) -> BTreeMap<String, String> {
    walkdir::WalkDir::new(example.join("src"))
        .into_iter()
        .flatten()
        .filter(|entry| entry.file_type().is_file())
        .filter(|entry| entry.path().to_string_lossy().ends_with(".lex.tex"))
        .map(|entry| {
            let relative = entry
                .path()
                .strip_prefix(example)
                .expect("under example")
                .to_string_lossy()
                .into_owned();
            let source = std::fs::read_to_string(entry.path()).expect("module source");
            (relative, source)
        })
        .collect()
}

/// §23.5: the formatter is idempotent over legal whitespace variance of
/// every example (fmt then fmt changes nothing), and reaches the committed
/// canonical bytes of every module: blank-line padding between blocks,
/// CRLF line endings, and surplus final line feeds all format back to the
/// committed source.
#[test]
fn formatter_is_idempotent_on_every_example() {
    let Some(root) = repo_root() else {
        return;
    };
    let mut examples: Vec<std::path::PathBuf> = std::fs::read_dir(root.join("examples"))
        .expect("examples")
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| path.join("lexlean.toml").is_file())
        .collect();
    examples.sort();
    assert!(
        examples.len() >= 4,
        "every example is exercised: {examples:?}"
    );
    /// One legal whitespace variance of a committed module.
    type Variant = fn(&str) -> String;
    let variants: [(&str, Variant); 4] = [
        ("committed", |source: &str| source.to_owned()),
        ("padded", |source: &str| {
            source.replace("\n\\begin{theorem}", "\n\n\n\\begin{theorem}")
        }),
        ("crlf", |source: &str| source.replace('\n', "\r\n")),
        ("surplus final LFs", |source: &str| format!("{source}\n\n")),
    ];
    for example in &examples {
        let modules = example_modules(example);
        assert!(!modules.is_empty(), "{}: modules", example.display());
        for (label, variant) in variants {
            let temp = tempfile::tempdir().expect("tempdir");
            copy_example(example, temp.path());
            for (relative, source) in &modules {
                std::fs::write(temp.path().join(relative), variant(source)).expect("write");
            }
            let config =
                camino::Utf8PathBuf::from_path_buf(temp.path().join("lexlean.toml")).expect("utf8");
            let engine = lexlean::Engine::load(&config).expect("loads");
            let format = |engine: &lexlean::Engine| {
                engine
                    .format(lexlean::FormatRequest {
                        selection: lexlean::Selection::All,
                        check_only: false,
                    })
                    .unwrap_or_else(|error| {
                        panic!("{}: {label}: fmt: {error:#?}", example.display())
                    });
            };
            format(&engine);
            let after_one: BTreeMap<String, String> = modules
                .keys()
                .map(|relative| {
                    (
                        relative.clone(),
                        std::fs::read_to_string(temp.path().join(relative)).expect("read"),
                    )
                })
                .collect();
            format(&engine);
            let after_two: BTreeMap<String, String> = modules
                .keys()
                .map(|relative| {
                    (
                        relative.clone(),
                        std::fs::read_to_string(temp.path().join(relative)).expect("read"),
                    )
                })
                .collect();
            assert_eq!(
                after_one,
                after_two,
                "{}: {label}: fmt is idempotent",
                example.display()
            );
            assert_eq!(
                after_one,
                modules,
                "{}: {label}: fmt reaches the committed canonical bytes",
                example.display()
            );
        }
    }
}
