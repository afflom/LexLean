//! The `lexicon` suite: GL-01..GL-16.

use lexlean::LockRequest;

use crate::support::{self, P};

/// Lock a mutated project, expecting the given diagnostic code.
fn lock_fails_with(project: &P, code: &str) -> lexlean::error::LexLeanError {
    let error = project
        .engine()
        .lock(LockRequest {
            check_only: false,
            allow_network: false,
        })
        .err()
        .expect("lock fails");
    support::expect_code(&error, code);
    error
}

/// Package-closure problems surface when the closure is built: lock the
/// mutated project, then expect `code` from check.
fn closure_fails_with(project: &P, code: &str) -> lexlean::error::LexLeanError {
    project.relock();
    project.check_fails_with(code)
}

/// A minimal valid entry with the given ID and unique math surface.
fn atom_entry(id: &str) -> String {
    format!(
        r#"spec = "lexlean/entry/1"
id = "{id}"
category = "term-constant"
signature = "(const lexlean.std.nat::nat)"
surface_arity = 0
frame = "atom"

[denotation]
kind = "lean"
module = "Init"
name = "Nat.zero"

[[form]]
id = "{id}"
channel = "both"
surface = "{id}"
canonical_source = true
features = []

[render]
math = "(operator-name {id})"
"#
    )
}

/// A project with one path package built from the given entry files.
fn with_entries(entries: &[(&str, &str)]) -> P {
    let project = P::example();
    project.add_package(
        "lexicons/test-pkg",
        "test.pkg",
        &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
        entries,
    );
    project
}

/// One mutated copy of the minimal entry, produced by string replacement.
fn mutated_entry(from: &str, to: &str) -> String {
    let base = atom_entry("probe");
    assert!(base.contains(from), "entry fixture lacks {from:?}");
    base.replacen(from, to, 1)
}

pub(crate) fn run(id: &str) {
    match id {
        // §13.1: layout, schema, ID-to-path, exact imports.
        "GL-01" => {
            let misplaced = with_entries(&[("elsewhere.toml", &atom_entry("probe"))]);
            lock_fails_with(&misplaced, "LLR3004");

            let wrong_version = P::example();
            wrong_version.add_package(
                "lexicons/test-pkg",
                "test.pkg",
                &["lexlean.core@2.0.0"],
                &[("probe.toml", &atom_entry("probe"))],
            );
            let error = wrong_version
                .engine()
                .lock(LockRequest {
                    check_only: false,
                    allow_network: false,
                })
                .err()
                .expect("an import at an unavailable exact version fails");
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLR3001" | "LLR3004")),
                "found {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
        }
        // §13.2: the exact entry schema with category-specific rules.
        "GL-02" => {
            let unknown = with_entries(&[(
                "probe.toml",
                &mutated_entry("surface_arity = 0", "surface_arity = 0\nmystery = true"),
            )]);
            lock_fails_with(&unknown, "LLR3004");

            let bad_category = with_entries(&[(
                "probe.toml",
                &mutated_entry("category = \"term-constant\"", "category = \"noun\""),
            )]);
            lock_fails_with(&bad_category, "LLR3004");

            let core_only = with_entries(&[(
                "probe.toml",
                &mutated_entry("category = \"term-constant\"", "category = \"grammar\""),
            )]);
            lock_fails_with(&core_only, "LLR3004");
        }
        // §13.5: forms carry channel, features, and canonical sourcing.
        "GL-03" => {
            let padded = with_entries(&[(
                "probe.toml",
                &mutated_entry("surface = \"probe\"", "surface = \" probe\""),
            )]);
            lock_fails_with(&padded, "LLR3004");

            let feature = with_entries(&[(
                "probe.toml",
                &mutated_entry("features = []", "features = [\"sideways\"]"),
            )]);
            lock_fails_with(&feature, "LLR3004");

            let no_canonical = with_entries(&[(
                "probe.toml",
                &mutated_entry("canonical_source = true", "canonical_source = false"),
            )]);
            lock_fails_with(&no_canonical, "LLR3004");
        }
        // §13.4: one fixed frame per entry; no package-defined grammar.
        "GL-04" => {
            let unknown_frame = with_entries(&[(
                "probe.toml",
                &mutated_entry("frame = \"atom\"", "frame = \"macro\""),
            )]);
            lock_fails_with(&unknown_frame, "LLR3004");

            let mismatched = with_entries(&[(
                "probe.toml",
                &mutated_entry("frame = \"atom\"", "frame = \"call\""),
            )]);
            lock_fails_with(&mismatched, "LLR3004");
        }
        // §13.6: denotations are exactly core, lean, document, or defined.
        "GL-05" => {
            let unknown_kind = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "kind = \"lean\"\nmodule = \"Init\"\nname = \"Nat.zero\"",
                    "kind = \"magic\"",
                ),
            )]);
            lock_fails_with(&unknown_kind, "LLR3004");

            let core_outside = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "kind = \"lean\"\nmodule = \"Init\"\nname = \"Nat.zero\"",
                    "kind = \"core\"\nconstructor = \"logic.eq\"",
                ),
            )]);
            lock_fails_with(&core_outside, "LLR3004");
        }
        // §13.8: valid, scoped, canonical LSE signatures.
        "GL-06" => {
            let unbound = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "signature = \"(const lexlean.std.nat::nat)\"",
                    "signature = \"(local ghost)\"",
                ),
            )]);
            lock_fails_with(&unbound, "LLR3004");

            let no_signature = with_entries(&[(
                "probe.toml",
                &mutated_entry("signature = \"(const lexlean.std.nat::nat)\"\n", ""),
            )]);
            lock_fails_with(&no_signature, "LLR3004");
        }
        // §13.9: complete slot use and no raw TeX in LRE.
        "GL-07" => {
            let out_of_range = with_entries(&[(
                "probe.toml",
                &mutated_entry("math = \"(operator-name probe)\"", "math = \"(slot 0)\""),
            )]);
            lock_fails_with(&out_of_range, "LLR3004");
        }
        // §13.10: only the core registry authorizes output controls.
        "GL-08" => {
            let bad_token = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "math = \"(operator-name probe)\"",
                    "math = \"(token unregistered-token)\"",
                ),
            )]);
            closure_fails_with(&bad_token, "LLR3004");

            let registry = support::repo_root().join("language/renderer-tokens.toml");
            let text = std::fs::read_to_string(registry.as_std_path()).expect("registry");
            let rows = text.matches("[[token]]").count();
            assert!(
                rows >= 70,
                "the closed core registry is committed ({rows} rows)"
            );
        }
        // §13.1: import cycles and excessive depth.
        "GL-09" => {
            let cyclic = P::example();
            cyclic.add_package(
                "lexicons/test-cyca",
                "test.cyca",
                &["lexlean.core@1.0.0", "test.cycb@1.0.0"],
                &[("cyca.toml", &atom_entry("cyca"))],
            );
            cyclic.add_package(
                "lexicons/test-cycb",
                "test.cycb",
                &["lexlean.core@1.0.0", "test.cyca@1.0.0"],
                &[("cycb.toml", &atom_entry("cycb"))],
            );
            closure_fails_with(&cyclic, "LLR3003");

            let deep = P::example();
            deep.edit(
                "lexlean.toml",
                "max_import_depth = 128",
                "max_import_depth = 3",
            );
            let mut previous: Option<String> = None;
            for index in 1..=6u32 {
                let name = format!("test.chain{index}");
                let file = format!("chain{index}.toml");
                let content = atom_entry(&format!("chain{index}"));
                let imports: Vec<String> = match &previous {
                    Some(parent) => vec!["lexlean.core@1.0.0".to_owned(), parent.clone()],
                    None => vec!["lexlean.core@1.0.0".to_owned()],
                };
                let import_refs: Vec<&str> = imports.iter().map(String::as_str).collect();
                deep.add_package(
                    &format!("lexicons/test-chain{index}"),
                    &name,
                    &import_refs,
                    &[(file.as_str(), content.as_str())],
                );
                previous = Some(format!("{name}@1.0.0"));
            }
            deep.relock();
            let error = deep.check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLS8002" | "LLR3003")),
                "excessive import depth is rejected: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
        }
        // §13.6: defined-denotation cycles are rejected.
        "GL-10" => {
            let entry = |name: &str, other: &str| {
                format!(
                    r#"spec = "lexlean/entry/1"
id = "{name}"
category = "term-constant"
signature = "(const lexlean.std.nat::nat)"
surface_arity = 0
frame = "atom"

[denotation]
kind = "defined"
value = "(const test.pkg::{other})"

[[form]]
id = "{name}"
channel = "both"
surface = "{name}"
canonical_source = true
features = []

[render]
math = "(operator-name {name})"
"#
                )
            };
            let cyclic = with_entries(&[
                ("cyca.toml", &entry("cyca", "cycb")),
                ("cycb.toml", &entry("cycb", "cyca")),
            ]);
            closure_fails_with(&cyclic, "LLR3003");
        }
        // §13.6: document denotations resolve with matching signatures.
        "GL-11" => {
            support::defs_project().check_ok();

            let mismatched = support::defs_project();
            mismatched.edit(
                "lexicons/test-defs/entries/double.toml",
                "component = \"double\"",
                "component = \"elsewhere\"",
            );
            mismatched.relock();
            mismatched.check_fails_with("LLF5001");
        }
        // §18.8: every used external entry is probed during verification.
        "GL-12" => {
            let fixture = support::verified();
            let checked = support::checked_project(&fixture.project);
            let probe_dir = fixture.outcome.root.join("probe");
            let probe_file = support::file_set(&probe_dir)
                .into_iter()
                .find(|name| name.ends_with(".lean"))
                .expect("the probe module is published");
            let probe_text =
                std::fs::read_to_string(probe_dir.join(&probe_file).as_std_path()).expect("read");
            assert!(
                !checked.external_used.is_empty(),
                "the example uses external entries"
            );
            for external in checked.external_used.values() {
                assert!(
                    probe_text.contains(&external.lean_name),
                    "the probe elaborates `{}`",
                    external.lean_name
                );
            }
        }
        // §13.11: duplicates rejected; overloads stay explicit candidates.
        "GL-13" => {
            let duplicated_package = P::example();
            duplicated_package.add_package(
                "lexicons/test-pkg",
                "test.pkg",
                &["lexlean.core@1.0.0"],
                &[("probe.toml", &atom_entry("probe"))],
            );
            duplicated_package.add_lexicon_source("test.pkg", "lexicons/test-pkg");
            let error = lexlean::Engine::load(&duplicated_package.root.join("lexlean.toml"))
                .err()
                .expect("a duplicate package row is rejected");
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLR3002" | "LLC0101")),
                "found {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );

            let duplicated_form = with_entries(&[(
                "probe.toml",
                &atom_entry("probe").replace(
                    "[render]",
                    "[[form]]\nid = \"probe\"\nchannel = \"both\"\nsurface = \"probed\"\ncanonical_source = false\nfeatures = []\n\n[render]",
                ),
            )]);
            lock_fails_with(&duplicated_form, "LLR3004");

            // Same-surface entries in two packages lock cleanly; ambiguity
            // arises only at use (LX-13).
            let overloads = P::example();
            overloads.add_package(
                "lexicons/test-dupa",
                "test.dupa",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[("nzz.toml", &support::nzz_entry("Nat.le_refl"))],
            );
            overloads.add_package(
                "lexicons/test-dupb",
                "test.dupb",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[("nzz.toml", &support::nzz_entry("Nat.ge_refl"))],
            );
            overloads.relock();
            overloads.check_ok();
        }
        // §16.11: eliminator descriptors validate structurally.
        "GL-14" => {
            let nat_entry = std::fs::read_to_string(
                support::repo_root()
                    .join("language/std/nat/entries/nat.toml")
                    .as_std_path(),
            )
            .expect("nat entry");
            assert!(
                nat_entry.contains("[eliminator]")
                    && nat_entry.contains("Nat.rec")
                    && nat_entry.contains("Nat.casesOn"),
                "nat carries a complete eliminator descriptor"
            );

            let duplicated = with_entries(&[(
                "gadget.toml",
                &nat_entry
                    .replace("id = \"nat\"", "id = \"gadget\"")
                    .replace("surface = \"natural number\"", "surface = \"gadget\"")
                    .replace(
                        "entry = \"lexlean.std.nat::succ\"",
                        "entry = \"lexlean.std.nat::zero\"",
                    ),
            )]);
            lock_fails_with(&duplicated, "LLR3004");
        }
        // §13.2: no free prose fields anywhere in glossary files.
        "GL-15" => {
            for field in ["description", "documentation", "note", "meaning"] {
                let prose = with_entries(&[(
                    "probe.toml",
                    &mutated_entry(
                        "surface_arity = 0",
                        &format!("surface_arity = 0\n{field} = \"free prose\""),
                    ),
                )]);
                lock_fails_with(&prose, "LLR3004");
            }
        }
        // §13.1, §21.4: bytes participate in lock and closure hashes.
        "GL-16" => {
            let project = with_entries(&[("probe.toml", &atom_entry("probe"))]);
            project.edit(
                "src/Main.lex.tex",
                "\\useglossary{lexlean.std.nat@1.0.0}",
                "\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.pkg@1.0.0}",
            );
            project.relock();
            let lock_before = project.read("lexlean.lock");
            let semantic_before = support::checked_project(&project).semantic_id;

            // A pure byte change flips the locked tree digest.
            let entry_path = "lexicons/test-pkg/entries/probe.toml";
            let text = project.read(entry_path);
            project.write(entry_path, &format!("{text}\n"));
            project.relock();
            assert_ne!(
                project.read("lexlean.lock"),
                lock_before,
                "§11.5: package bytes flow into the lock digest"
            );

            // A semantic change flips the semantic ID.
            project.edit(entry_path, "surface = \"probe\"", "surface = \"probed\"");
            project.relock();
            assert_ne!(
                support::checked_project(&project).semantic_id,
                semantic_before,
                "§21.4: entry content flows into the semantic ID"
            );
        }
        other => panic!("no lexicon case is wired for {other}"),
    }
}
