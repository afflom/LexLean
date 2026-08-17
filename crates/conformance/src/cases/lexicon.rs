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
        // §13.1: layout, schema, ID-to-path, exact imports, import closure.
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

            // Comments and unknown fields in lexicon.toml are errors.
            let commented = with_entries(&[("probe.toml", &atom_entry("probe"))]);
            commented.edit(
                "lexicons/test-pkg/lexicon.toml",
                "language = \"1.0\"",
                "language = \"1.0\" # the language",
            );
            lock_fails_with(&commented, "LLR3004");
            let unknown_field = with_entries(&[("probe.toml", &atom_entry("probe"))]);
            unknown_field.edit(
                "lexicons/test-pkg/lexicon.toml",
                "language = \"1.0\"",
                "language = \"1.0\"\nauthor = \"nobody\"",
            );
            lock_fails_with(&unknown_field, "LLR3004");

            // Imports sort bytewise as `package@version` text.
            let unsorted = P::example();
            unsorted.add_package(
                "lexicons/test-pkg",
                "test.pkg",
                &["lexlean.std.nat@1.0.0", "lexlean.core@1.0.0"],
                &[("probe.toml", &atom_entry("probe"))],
            );
            lock_fails_with(&unsorted, "LLR3004");
            let duplicated = P::example();
            duplicated.add_package(
                "lexicons/test-pkg",
                "test.pkg",
                &["lexlean.core@1.0.0", "lexlean.core@1.0.0"],
                &[("probe.toml", &atom_entry("probe"))],
            );
            lock_fails_with(&duplicated, "LLR3004");

            // References resolve only within the package's transitive import
            // closure: a package that imports nothing cannot see std.nat, and
            // a package that imports only core cannot see std.nat either.
            let isolated = P::example();
            isolated.add_package(
                "lexicons/test-pkg",
                "test.pkg",
                &[],
                &[("probe.toml", &atom_entry("probe"))],
            );
            let error = closure_fails_with(&isolated, "LLR3005");
            let message = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLR3005")
                .map(|d| d.message.clone())
                .unwrap_or_default();
            assert!(
                message.contains("lexlean.std.nat::nat") && message.contains("import closure"),
                "the diagnostic names the reference and the closure: {message}"
            );
            let core_only = P::example();
            core_only.add_package(
                "lexicons/test-pkg",
                "test.pkg",
                &["lexlean.core@1.0.0"],
                &[("probe.toml", &atom_entry("probe"))],
            );
            closure_fails_with(&core_only, "LLR3005");
            // The transitive closure suffices: importing a package that
            // imports std.nat brings std.nat into view.
            let transitive = P::example();
            transitive.add_package(
                "lexicons/test-mid",
                "test.mid",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[("mid.toml", &atom_entry("mid"))],
            );
            transitive.add_package(
                "lexicons/test-pkg",
                "test.pkg",
                &["lexlean.core@1.0.0", "test.mid@1.0.0"],
                &[("probe.toml", &atom_entry("probe"))],
            );
            transitive.relock();
            transitive.check_ok();
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

            // surface_arity must equal the explicit binders of the signature.
            let arity = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "signature = \"(const lexlean.std.nat::nat)\"",
                    "signature = \"(pi ((explicit n (const lexlean.std.nat::nat))) (const lexlean.std.nat::nat))\"",
                ),
            )]);
            let error = lock_fails_with(&arity, "LLR3004");
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| d.message.contains("surface_arity 0") && d.message.contains("probe")),
                "the arity diagnostic names the entry and the arity: {error}"
            );

            // A text render does not apply to a math-only category.
            let text_render = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "category = \"term-constant\"",
                    "category = \"predicate-constant\"",
                )
                .replace(
                    "math = \"(operator-name probe)\"",
                    "math = \"(operator-name probe)\"\ntext = \"(self-form probe)\"",
                ),
            )]);
            lock_fails_with(&text_render, "LLR3004");
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

            let unsorted_features = with_entries(&[(
                "probe.toml",
                &mutated_entry("features = []", "features = [\"singular\", \"lower-case\"]"),
            )]);
            lock_fails_with(&unsorted_features, "LLR3004");

            let no_canonical = with_entries(&[(
                "probe.toml",
                &mutated_entry("canonical_source = true", "canonical_source = false"),
            )]);
            lock_fails_with(&no_canonical, "LLR3004");

            let two_canonical = with_entries(&[(
                "probe.toml",
                &atom_entry("probe").replace(
                    "[render]",
                    "[[form]]\nid = \"probe-two\"\nchannel = \"both\"\nsurface = \"probed\"\ncanonical_source = true\nfeatures = []\n\n[render]",
                ),
            )]);
            lock_fails_with(&two_canonical, "LLR3004");

            // A control-sequence form is an alias only for non-core entries.
            let control_canonical = with_entries(&[(
                "probe.toml",
                &mutated_entry("surface = \"probe\"", "surface = \"\\\\probe\""),
            )]);
            lock_fails_with(&control_canonical, "LLR3004");

            // Rules 4 and 5: an unsafe canonical surface is LLR3006.
            for unsafe_surface in [
                "pr{obe}",
                "pr$obe",
                "pr\\\\relax",
                "probe%",
                "x_1",
                "\\\"q\\\"",
            ] {
                let unsafe_canonical = with_entries(&[(
                    "probe.toml",
                    &mutated_entry(
                        "surface = \"probe\"",
                        &format!("surface = \"{unsafe_surface}\""),
                    ),
                )]);
                let error = lock_fails_with(&unsafe_canonical, "LLR3006");
                let _ = error;
            }
            let text_symbol = with_entries(&[(
                "probe.toml",
                &mutated_entry("surface = \"probe\"", "surface = \"pr+obe\"")
                    .replace("channel = \"both\"", "channel = \"text\"")
                    .replace("[render]\nmath = \"(operator-name probe)\"\n", ""),
            )]);
            lock_fails_with(&text_symbol, "LLR3006");
            let math_symbol = with_entries(&[(
                "probe.toml",
                &mutated_entry("surface = \"probe\"", "surface = \"pr+obe\"")
                    .replace("channel = \"both\"", "channel = \"math\"")
                    .replace(
                        "category = \"term-constant\"",
                        "category = \"predicate-constant\"",
                    )
                    .replace(
                        "signature = \"(const lexlean.std.nat::nat)\"",
                        "signature = \"(sort prop)\"",
                    ),
            )]);
            math_symbol.relock();
            math_symbol.check_ok();

            // A non-canonical alias is either renderer-safe or exactly one
            // control sequence (§13.5 rule 3, an input-only spelling); a
            // mixed raw-TeX alias is rejected at load whether or not an LRE
            // references it (§13.9: raw TeX strings do not exist).
            let control_alias = with_entries(&[(
                "probe.toml",
                &atom_entry("probe").replace(
                    "[render]",
                    "[[form]]\nid = \"alias\"\nchannel = \"math\"\nsurface = \"\\\\probe\"\ncanonical_source = false\nfeatures = []\n\n[render]",
                ),
            )]);
            control_alias.relock();
            control_alias.check_ok();
            let raw_alias = with_entries(&[(
                "probe.toml",
                &atom_entry("probe").replace(
                    "[render]",
                    "[[form]]\nid = \"alias\"\nchannel = \"math\"\nsurface = \"\\\\jobname{x} $ \\\\relax\"\ncanonical_source = false\nfeatures = []\n\n[render]",
                ),
            )]);
            lock_fails_with(&raw_alias, "LLR3006");
            // An LRE that references a control alias (self-form or a
            // cross-package form) is rejected: the referenced form must be
            // renderer-safe.
            let self_injected = with_entries(&[(
                "probe.toml",
                &atom_entry("probe")
                    .replace(
                        "[render]",
                        "[[form]]\nid = \"alias\"\nchannel = \"math\"\nsurface = \"\\\\probe\"\ncanonical_source = false\nfeatures = []\n\n[render]",
                    )
                    .replace("math = \"(operator-name probe)\"", "math = \"(self-form alias)\""),
            )]);
            lock_fails_with(&self_injected, "LLR3006");
            let cross_injected = P::example();
            cross_injected.add_package(
                "lexicons/test-other",
                "test.other",
                &[
                    "lexlean.core@1.0.0",
                    "lexlean.std.nat@1.0.0",
                    "test.pkg@1.0.0",
                ],
                &[(
                    "other.toml",
                    &atom_entry("other").replace(
                        "math = \"(operator-name other)\"",
                        "math = \"(form test.pkg::probe alias)\"",
                    ),
                )],
            );
            cross_injected.add_package(
                "lexicons/test-pkg",
                "test.pkg",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[(
                    "probe.toml",
                    &atom_entry("probe").replace(
                        "[render]",
                        "[[form]]\nid = \"alias\"\nchannel = \"math\"\nsurface = \"\\\\probe\"\ncanonical_source = false\nfeatures = []\n\n[render]",
                    ),
                )],
            );
            closure_fails_with(&cross_injected, "LLR3006");

            // A brace is never a renderer-safe alias surface (§13.5).
            let brace_alias = with_entries(&[(
                "probe.toml",
                &atom_entry("probe").replace(
                    "[render]",
                    "[[form]]\nid = \"alias\"\nchannel = \"both\"\nsurface = \"}\"\ncanonical_source = false\nfeatures = []\n\n[render]",
                ),
            )]);
            lock_fails_with(&brace_alias, "LLR3006");
            // Core structural and grammar surfaces are reserved.
            for reserved in ["\\\\begin", "\\\\lexeme", "the", "of"] {
                let aliased = with_entries(&[(
                    "probe.toml",
                    &atom_entry("probe").replace(
                        "[render]",
                        &format!(
                            "[[form]]\nid = \"alias\"\nchannel = \"both\"\nsurface = \"{reserved}\"\ncanonical_source = false\nfeatures = []\n\n[render]"
                        ),
                    ),
                )]);
                closure_fails_with(&aliased, "LLR3002");
            }
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
        // §13.8: valid, scoped, canonical, well-typed LSE signatures.
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

            // Every grammar production parses and canonicalizes; alpha-
            // equivalent signatures hash identically.
            let full = String::from(
                "(pi ((implicit a (sort (type (max u (succ 0) (imax u 1))))) (explicit f (pi ((explicit x (local a))) (sort prop))) (explicit n (local a))) (let m (local a) (local n) (app (local f) (local m))))"
            );
            let productions = with_entries(&[
                (
                    "probe.toml",
                    &atom_entry("probe")
                        .replace(
                            "signature = \"(const lexlean.std.nat::nat)\"",
                            &format!("signature = \"{full}\"\nuniverses = [\"u\"]"),
                        )
                        .replace("surface_arity = 0", "surface_arity = 2")
                        .replace("frame = \"atom\"", "frame = \"call\"")
                        .replace("category = \"term-constant\"", "category = \"proof-constant\"")
                        .replace(
                            "math = \"(operator-name probe)\"",
                            "math = \"(seq (operator-name probe) (paren (seq (slot 0) (token comma) (slot 1))))\"",
                        ),
                ),
                (
                    "alpha.toml",
                    &atom_entry("alpha").replace(
                        "signature = \"(const lexlean.std.nat::nat)\"",
                        "signature = \"(pi ((explicit x (sort prop)) (explicit y (sort prop))) (local y))\"",
                    ).replace("surface_arity = 0", "surface_arity = 2")
                        .replace("frame = \"atom\"", "frame = \"call\"")
                        .replace("category = \"term-constant\"", "category = \"proof-constant\"")
                        .replace(
                            "math = \"(operator-name alpha)\"",
                            "math = \"(seq (operator-name alpha) (paren (seq (slot 0) (token comma) (slot 1))))\"",
                        ),
                ),
                (
                    "beta.toml",
                    &atom_entry("beta").replace(
                        "signature = \"(const lexlean.std.nat::nat)\"",
                        "signature = \"(pi ((explicit p (sort prop)) (explicit q (sort prop))) (local q))\"",
                    ).replace("surface_arity = 0", "surface_arity = 2")
                        .replace("frame = \"atom\"", "frame = \"call\"")
                        .replace("category = \"term-constant\"", "category = \"proof-constant\"")
                        .replace(
                            "math = \"(operator-name beta)\"",
                            "math = \"(seq (operator-name beta) (paren (seq (slot 0) (token comma) (slot 1))))\"",
                        ),
                ),
            ]);
            productions.relock();
            let checked = support::checked_project(&productions);
            let entry = |id: &str| {
                checked
                    .closure
                    .entry(
                        &lexlean::lexicon::lse::QualifiedId::parse(&format!("test.pkg::{id}"))
                            .expect("id"),
                    )
                    .expect("entry")
                    .clone()
            };
            assert_eq!(
                entry("probe").signature_canonical.as_deref(),
                Some(
                    "(pi ((implicit x0 (sort (type (max u (succ 0) (imax u 1))))) (explicit x1 (pi ((explicit x2 (local x0))) (sort prop))) (explicit x3 (local x0))) (let x4 (local x0) (local x3) (app (local x1) (local x4))))"
                ),
                "canonical LSE: one space, no redundant grouping, binders x0.."
            );
            assert_eq!(
                entry("alpha").signature_hash,
                entry("beta").signature_hash,
                "alpha-equivalent signatures hash identically"
            );

            // A signature must be type-shaped.
            let not_a_type = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "signature = \"(const lexlean.std.nat::nat)\"",
                    "signature = \"(nat 3)\"",
                ),
            )]);
            closure_fails_with(&not_a_type, "LLR3004");
            let term_not_type = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "signature = \"(const lexlean.std.nat::nat)\"",
                    "signature = \"(const lexlean.std.nat::zero)\"",
                ),
            )]);
            closure_fails_with(&term_not_type, "LLR3004");
            let no_signature_ref = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "signature = \"(const lexlean.std.nat::nat)\"",
                    "signature = \"(const lexlean.core::the)\"",
                ),
            )]);
            closure_fails_with(&no_signature_ref, "LLR3004");

            // Applications supply at most the explicit binders (S5): `eq`
            // has one implicit and two explicit binders.
            let over_applied = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "signature = \"(const lexlean.std.nat::nat)\"",
                    "signature = \"(app (const lexlean.core::eq) (const lexlean.std.nat::zero) (const lexlean.std.nat::zero) (const lexlean.std.nat::zero))\"",
                )
                .replace("category = \"term-constant\"", "category = \"predicate-constant\""),
            )]);
            let error = closure_fails_with(&over_applied, "LLR3004");
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| d.message.contains("test.pkg::probe")
                        && d.message.contains("3 explicit")),
                "the diagnostic names the entry and the arity: {error}"
            );
            let well_applied = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "signature = \"(const lexlean.std.nat::nat)\"",
                    "signature = \"(app (const lexlean.core::eq) (const lexlean.std.nat::zero) (nat 0))\"",
                )
                .replace("category = \"term-constant\"", "category = \"predicate-constant\""),
            )]);
            well_applied.relock();
            well_applied.check_ok();
            let mistyped_arg = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "signature = \"(const lexlean.std.nat::nat)\"",
                    "signature = \"(app (const lexlean.std.nat::le) (const lexlean.std.nat::zero) (const lexlean.std.nat::nat))\"",
                )
                .replace("category = \"term-constant\"", "category = \"predicate-constant\""),
            )]);
            closure_fails_with(&mistyped_arg, "LLR3004");

            // Defined values must match their signatures.
            let defined = |value: &str| {
                atom_entry("probe")
                    .replace(
                        "signature = \"(const lexlean.std.nat::nat)\"",
                        "signature = \"(pi ((explicit a (const lexlean.std.nat::nat)) (explicit b (const lexlean.std.nat::nat))) (const lexlean.std.nat::nat))\"",
                    )
                    .replace("category = \"term-constant\"", "category = \"infix-function\"")
                    .replace("frame = \"atom\"", "frame = \"infix\"\nprecedence = 65\nassociativity = \"left\"")
                    .replace("surface_arity = 0", "surface_arity = 2")
                    .replace("surface = \"probe\"", "surface = \"⊕\"")
                    .replace("channel = \"both\"", "channel = \"math\"")
                    .replace(
                        "kind = \"lean\"\nmodule = \"Init\"\nname = \"Nat.zero\"",
                        &format!("kind = \"defined\"\nvalue = \"{value}\""),
                    )
                    .replace(
                        "math = \"(operator-name probe)\"",
                        "math = \"(seq (slot 0) (space) (token plus) (space) (slot 1))\"",
                    )
            };
            let good = with_entries(&[(
                "probe.toml",
                &defined("(lam ((explicit x (const lexlean.std.nat::nat)) (explicit y (const lexlean.std.nat::nat))) (app (const lexlean.std.nat::add) (local y) (local x)))"),
            )]);
            good.relock();
            good.check_ok();
            let wrong_binder = with_entries(&[(
                "probe.toml",
                &defined("(lam ((explicit x (const lexlean.std.nat::nat)) (explicit y (sort prop))) (local x))"),
            )]);
            closure_fails_with(&wrong_binder, "LLR3004");
            let wrong_body = with_entries(&[(
                "probe.toml",
                &defined("(lam ((explicit x (const lexlean.std.nat::nat)) (explicit y (const lexlean.std.nat::nat))) (app (const lexlean.std.nat::le) (local x) (local y)))"),
            )]);
            closure_fails_with(&wrong_body, "LLR3004");
            let too_few = with_entries(&[(
                "probe.toml",
                &defined("(lam ((explicit x (const lexlean.std.nat::nat))) (local x))"),
            )]);
            closure_fails_with(&too_few, "LLR3004");

            // Nesting is bounded by max_scope_depth, an explicit limit.
            let deep = with_entries(&[(
                "probe.toml",
                &mutated_entry(
                    "signature = \"(const lexlean.std.nat::nat)\"",
                    &format!(
                        "signature = \"{}(const lexlean.std.nat::nat){}\"",
                        "(app ".repeat(200_000),
                        ")".repeat(200_000)
                    ),
                ),
            )]);
            lock_fails_with(&deep, "LLS8002");
        }
        // §13.9: complete slot use, valid references, and no raw TeX in LRE.
        "GL-07" => {
            let out_of_range = with_entries(&[(
                "probe.toml",
                &mutated_entry("math = \"(operator-name probe)\"", "math = \"(slot 0)\""),
            )]);
            lock_fails_with(&out_of_range, "LLR3004");

            let call = |render: &str| {
                atom_entry("probe")
                    .replace(
                        "signature = \"(const lexlean.std.nat::nat)\"",
                        "signature = \"(pi ((explicit a (const lexlean.std.nat::nat)) (explicit b (const lexlean.std.nat::nat))) (const lexlean.std.nat::nat))\"",
                    )
                    .replace("category = \"term-constant\"", "category = \"function\"")
                    .replace("frame = \"atom\"", "frame = \"call\"")
                    .replace("surface_arity = 0", "surface_arity = 2")
                    .replace("channel = \"both\"", "channel = \"math\"")
                    .replace("math = \"(operator-name probe)\"", &format!("math = \"{render}\""))
            };
            let duplicate_slot = with_entries(&[(
                "probe.toml",
                &call("(seq (operator-name probe) (paren (seq (slot 0) (token comma) (slot 0))))"),
            )]);
            lock_fails_with(&duplicate_slot, "LLR3004");
            let missing_slot = with_entries(&[(
                "probe.toml",
                &call("(seq (operator-name probe) (paren (slot 1)))"),
            )]);
            lock_fails_with(&missing_slot, "LLR3004");
            let noncanonical_slot = with_entries(&[(
                "probe.toml",
                &call("(seq (operator-name probe) (paren (seq (slot 0) (token comma) (slot 01))))"),
            )]);
            lock_fails_with(&noncanonical_slot, "LLR3004");
            let raw = with_entries(&[(
                "probe.toml",
                &call("(seq (raw \\\\relax) (slot 0) (slot 1))"),
            )]);
            lock_fails_with(&raw, "LLR3004");
            let bad_operator = with_entries(&[(
                "probe.toml",
                &call("(seq (operator-name pr-obe) (paren (seq (slot 0) (token comma) (slot 1))))"),
            )]);
            lock_fails_with(&bad_operator, "LLR3004");
            let unknown_self_form = with_entries(&[(
                "probe.toml",
                &call("(seq (self-form ghost) (paren (seq (slot 0) (token comma) (slot 1))))"),
            )]);
            lock_fails_with(&unknown_self_form, "LLR3004");
            let unknown_form = with_entries(&[(
                "probe.toml",
                &call("(seq (form lexlean.std.nat::succ ghost) (paren (seq (slot 0) (token comma) (slot 1))))"),
            )]);
            closure_fails_with(&unknown_form, "LLR3004");
            let text_token = with_entries(&[(
                "probe.toml",
                &call("(seq (token theorem) (paren (seq (slot 0) (token comma) (slot 1))))"),
            )]);
            closure_fails_with(&text_token, "LLR3004");
            // sub, sup, and frac are grammar; their operands must render.
            let scripts = with_entries(&[(
                "probe.toml",
                &call("(seq (operator-name probe) (sub (slot 0) (group (sup (slot 1) (frac (token plus) (token minus))))))"),
            )]);
            scripts.relock();
            let empty_script = with_entries(&[(
                "probe.toml",
                &call("(seq (operator-name probe) (sub (slot 0) (space)) (slot 1))"),
            )]);
            lock_fails_with(&empty_script, "LLR3004");
            let deep_render = with_entries(&[(
                "probe.toml",
                &call(&format!(
                    "(seq (slot 0) (slot 1) {}(space){})",
                    "(group ".repeat(100_000),
                    ")".repeat(100_000)
                )),
            )]);
            lock_fails_with(&deep_render, "LLS8002");
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

            // The committed registry carries every §13.10 semantic ID with
            // the fixed canonical bytes, and every row is core-authored.
            let registry = lexlean::lexicon::load_token_registry().expect("registry loads");
            for (id, bytes) in [
                ("logical-and", "\\land"),
                ("logical-or", "\\lor"),
                ("logical-not", "\\lnot"),
                ("implies", "\\to"),
                ("iff", "\\leftrightarrow"),
                ("forall", "\\forall"),
                ("exists", "\\exists"),
                ("exists-unique", "\\exists!"),
                ("member", "\\in"),
                ("subset-equal", "\\subseteq"),
            ] {
                assert_eq!(
                    registry.get(id).map(|row| row.bytes.as_str()),
                    Some(bytes),
                    "§13.10 fixes the bytes of `{id}`"
                );
            }
            for id in [
                "documentclass",
                "usepackage",
                "newtheorem",
                "theoremstyle",
                "begin",
                "end",
                "center",
                "large",
                "section",
                "subsection",
                "label",
                "texttt",
                "operatorname",
                "mathbb",
                "mathrm",
                "proof",
                "definition",
                "theorem",
                "lemma",
                "corollary",
                "plus",
                "minus",
                "times",
                "cdot",
                "slash",
                "equals",
                "not-equals",
                "less",
                "less-equal",
                "greater",
                "greater-equal",
                "member",
                "not-member",
                "subset",
                "subset-equal",
                "union",
                "intersection",
                "forall",
                "exists",
                "exists-unique",
                "logical-and",
                "logical-or",
                "logical-not",
                "implies",
                "iff",
                "mapsto",
                "arrow",
                "left-arrow",
                "comma",
                "period",
                "colon",
                "semicolon",
                "left-paren",
                "right-paren",
                "left-bracket",
                "right-bracket",
            ] {
                let row = registry
                    .get(id)
                    .unwrap_or_else(|| panic!("required token `{id}`"));
                assert_eq!(row.authority, "lexlean.core");
                assert!(!row.bytes.is_empty());
            }
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
            for letter in ["a", "b", "c", "d", "e", "f"] {
                let name = format!("test.chain{letter}");
                let file = format!("chain{letter}.toml");
                let content = atom_entry(&format!("chain{letter}"));
                let imports: Vec<String> = match &previous {
                    Some(parent) => vec!["lexlean.core@1.0.0".to_owned(), parent.clone()],
                    None => vec!["lexlean.core@1.0.0".to_owned()],
                };
                let import_refs: Vec<&str> = imports.iter().map(String::as_str).collect();
                deep.add_package(
                    &format!("lexicons/test-chain{letter}"),
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
        // §16.11: eliminator descriptors validate structurally and against
        // the constructors' signatures.
        "GL-14" => {
            let nat_entry = std::fs::read_to_string(
                support::repo_root()
                    .join("language/std/nat/entries/nat.toml")
                    .as_std_path(),
            )
            .expect("nat entry");
            let project = P::example();
            let checked = support::checked_project(&project);
            let nat = checked
                .closure
                .entry(
                    &lexlean::lexicon::lse::QualifiedId::parse("lexlean.std.nat::nat").expect("id"),
                )
                .expect("nat");
            let eliminator = nat.eliminator.as_ref().expect("nat carries a descriptor");
            assert_eq!(eliminator.cases_lean_name, "Nat.casesOn");
            assert_eq!(eliminator.induction_lean_name, "Nat.rec");
            assert_eq!(
                eliminator
                    .constructors
                    .iter()
                    .map(|c| (
                        c.entry.to_string(),
                        c.lean_name.clone(),
                        c.fields.clone(),
                        c.induction_hypotheses.clone()
                    ))
                    .collect::<Vec<_>>(),
                vec![
                    (
                        "lexlean.std.nat::zero".to_owned(),
                        "Nat.zero".to_owned(),
                        vec![],
                        vec![]
                    ),
                    (
                        "lexlean.std.nat::succ".to_owned(),
                        "Nat.succ".to_owned(),
                        vec!["n".to_owned()],
                        vec!["ih".to_owned()]
                    ),
                ]
            );
            // Core connectives carry descriptors on their head entries.
            for (head, cases) in [
                ("lexlean.core::land", "And.casesOn"),
                ("lexlean.core::lor", "Or.casesOn"),
                ("lexlean.core::iff", "Iff.casesOn"),
                ("lexlean.core::exists-op", "Exists.casesOn"),
            ] {
                let id = lexlean::lexicon::lse::QualifiedId::parse(head).expect("id");
                let (_, descriptor) = checked
                    .closure
                    .eliminator_for(&id)
                    .unwrap_or_else(|| panic!("{head} carries a descriptor"));
                assert_eq!(descriptor.cases_lean_name, cases);
            }
            assert_eq!(
                checked
                    .closure
                    .core_entry_for_constructor("logic.or")
                    .map(|id| id.to_string()),
                Some("lexlean.core::lor".to_owned())
            );

            let gadget = |edit: &dyn Fn(String) -> String| {
                let text = nat_entry
                    .replace("id = \"nat\"", "id = \"gadget\"")
                    .replace("surface = \"natural number\"", "surface = \"gadget\"")
                    .replace("surface = \"Natural number\"", "surface = \"Gadget\"")
                    .replace("surface = \"natural numbers\"", "surface = \"gadgets\"")
                    .replace("surface = \"Natural numbers\"", "surface = \"Gadgets\"")
                    .replace("surface = \"ℕ\"", "surface = \"𝔾\"");
                edit(text)
            };
            let identity: &dyn Fn(String) -> String = &|t| t;
            // A foreign type's constructors are rejected: they construct
            // `nat`, not `gadget`.
            let foreign = with_entries(&[("gadget.toml", &gadget(identity))]);
            closure_fails_with(&foreign, "LLR3004");
            let duplicated = with_entries(&[(
                "gadget.toml",
                &gadget(&|t| {
                    t.replace(
                        "entry = \"lexlean.std.nat::succ\"",
                        "entry = \"lexlean.std.nat::zero\"",
                    )
                }),
            )]);
            lock_fails_with(&duplicated, "LLR3004");
            let absent = with_entries(&[(
                "gadget.toml",
                &gadget(&|t| {
                    t.replace(
                        "entry = \"lexlean.std.nat::succ\"",
                        "entry = \"lexlean.std.nat::ghost\"",
                    )
                }),
            )]);
            closure_fails_with(&absent, "LLR3004");
            let non_type = with_entries(&[(
                "probe.toml",
                &format!(
                    "{}\n[eliminator]\ncases_lean_name = \"Nat.casesOn\"\ninduction_lean_name = \"Nat.rec\"\n\n[[eliminator.constructor]]\nentry = \"lexlean.std.nat::zero\"\nlean_name = \"Nat.zero\"\nfields = []\ninduction_hypotheses = []\n",
                    atom_entry("probe")
                ),
            )]);
            lock_fails_with(&non_type, "LLR3004");

            // A well-formed local type with its own constructors.
            let zero_ctor = |name: &str, target: &str, extra: &str| {
                format!(
                    r#"spec = "lexlean/entry/1"
id = "{name}"
category = "term-constant"
signature = "(const test.pkg::{target})"
surface_arity = 0
frame = "atom"

[denotation]
kind = "lean"
module = "Init"
name = "Nat.zero"

[[form]]
id = "{name}"
channel = "both"
surface = "{name}"
canonical_source = true
features = []

[render]
math = "(operator-name {name})"
{extra}"#
                )
            };
            let succ_ctor = |fields_ty: &str| {
                format!(
                    r#"spec = "lexlean/entry/1"
id = "gsucc"
category = "function"
signature = "(pi ((explicit n {fields_ty})) (const test.pkg::gadget))"
surface_arity = 1
frame = "call"

[denotation]
kind = "lean"
module = "Init"
name = "Nat.succ"

[[form]]
id = "gsucc"
channel = "math"
surface = "gsucc"
canonical_source = true
features = []

[render]
math = "(seq (operator-name gsucc) (paren (slot 0)))"
"#
                )
            };
            let local_gadget = |fields: &str, hypotheses: &str| {
                gadget(&|t| {
                    t.replace(
                        "entry = \"lexlean.std.nat::zero\"",
                        "entry = \"test.pkg::gzero\"",
                    )
                    .replace(
                        "entry = \"lexlean.std.nat::succ\"",
                        "entry = \"test.pkg::gsucc\"",
                    )
                    .replace("fields = [\"n\"]", &format!("fields = [{fields}]"))
                    .replace(
                        "induction_hypotheses = [\"ih\"]",
                        &format!("induction_hypotheses = [{hypotheses}]"),
                    )
                })
            };
            let coherent = with_entries(&[
                ("gadget.toml", &local_gadget("\"n\"", "\"ih\"")),
                ("gzero.toml", &zero_ctor("gzero", "gadget", "")),
                ("gsucc.toml", &succ_ctor("(const test.pkg::gadget)")),
            ]);
            coherent.relock();
            coherent.check_ok();
            let wrong_fields = with_entries(&[
                ("gadget.toml", &local_gadget("\"n\", \"m\"", "\"ih\"")),
                ("gzero.toml", &zero_ctor("gzero", "gadget", "")),
                ("gsucc.toml", &succ_ctor("(const test.pkg::gadget)")),
            ]);
            closure_fails_with(&wrong_fields, "LLR3004");
            let wrong_hypotheses = with_entries(&[
                ("gadget.toml", &local_gadget("\"n\"", "\"ih\"")),
                ("gzero.toml", &zero_ctor("gzero", "gadget", "")),
                ("gsucc.toml", &succ_ctor("(const lexlean.std.nat::nat)")),
            ]);
            closure_fails_with(&wrong_hypotheses, "LLR3004");
            let bad_lean_name = with_entries(&[
                (
                    "gadget.toml",
                    &local_gadget("\"n\"", "\"ih\"")
                        .replace("lean_name = \"Nat.succ\"", "lean_name = \"Nat..succ\""),
                ),
                ("gzero.toml", &zero_ctor("gzero", "gadget", "")),
                ("gsucc.toml", &succ_ctor("(const test.pkg::gadget)")),
            ]);
            lock_fails_with(&bad_lean_name, "LLR3004");
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
