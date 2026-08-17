//! The reserved identifier-like tokens of the pinned Lean 4.32.1 toolchain
//! (SPEC.md §17.8): a component ID whose generated Lean name is one of these
//! is rejected, because Lean's identifier parser turns any identifier that
//! exactly matches a token-table entry into that token (`Lean.Parser.Basic`,
//! `mkIdResult`/`isToken`), so `theorem forall ...` fails to parse.
//!
//! The list is derived mechanically, not curated. It is the sorted set of
//! token-table entries that lex as identifiers (a letter, `_`, or a
//! letter-like character followed by identifier-rest characters, which in
//! Lean include `!` and `?`) after importing every root library the pinned
//! toolchain ships — `Init`, `Std`, and `Lean` — with extension entries
//! loaded, i.e. exactly the token table `lean` parses a file against once
//! those modules are imported. The probe was run once with the pinned
//! `lean` (`lean --run Tokens.lean Init Std Lean`, reading
//! `Lean.Parser.getTokenTable` over `importModules ... (loadExts := true)`),
//! and the module tests below re-check the pinned list against the
//! toolchain in its executable form: every listed token is refused as a
//! declaration name, and non-reserved tactic names are accepted.
//!
//! Tokens brought in by third-party imports (a Lake dependency's own
//! `syntax` declarations) are outside the toolchain and outside this list;
//! Lean itself reports such a collision at verification (§22.3).

/// Every identifier-like token of the pinned toolchain's `Init`, `Std`,
/// and `Lean` token tables, bytewise sorted and deduplicated.
pub const LEAN_RESERVED_TOKENS: &[&str] = &[
    "Prop",
    "Sort",
    "StateRefT",
    "Type",
    "_",
    "abbrev",
    "add_decl_doc",
    "assert!",
    "assert_not_exists",
    "assert_not_imported",
    "at",
    "attribute",
    "axiom",
    "bif",
    "binder_predicate",
    "break",
    "builtin_cbv_simproc",
    "builtin_cbv_simproc_decl",
    "builtin_dsimproc",
    "builtin_dsimproc_decl",
    "builtin_grind_propagator",
    "builtin_initialize",
    "builtin_simproc",
    "builtin_simproc_decl",
    "by",
    "by?",
    "by_elab",
    "calc",
    "catch",
    "cbv_eval",
    "cbv_simproc",
    "cbv_simproc_decl",
    "class",
    "coinductive",
    "coinductive_fixpoint",
    "continue",
    "dbg_trace",
    "debug_assert!",
    "declare_bitwise_int_theorems",
    "declare_bitwise_uint_theorems",
    "declare_command_config_elab",
    "declare_command_config_elab_legacy",
    "declare_config_elab",
    "declare_config_elab_legacy",
    "declare_core_config_elab",
    "declare_eval_bin",
    "declare_eval_bin_bitwise",
    "declare_eval_bin_bool_pred",
    "declare_int_theorems",
    "declare_simp_like_tactic",
    "declare_sint_simprocs",
    "declare_syntax_cat",
    "declare_term_config_elab",
    "declare_uint_simprocs",
    "declare_uint_theorems",
    "decreasing_by",
    "def",
    "def_eval_config_item",
    "deprecated_module",
    "deprecated_syntax",
    "deriving",
    "do",
    "docs_to_verso",
    "dsimproc",
    "dsimproc_decl",
    "elab",
    "elab_rules",
    "elab_stx_quot",
    "else",
    "end",
    "eval_prec",
    "eval_prio",
    "example",
    "exists",
    "export",
    "extends",
    "f!",
    "finally",
    "for",
    "forall",
    "from",
    "fun",
    "generalizing",
    "grind_annotated",
    "grind_pattern",
    "grind_propagator",
    "have",
    "haveI",
    "hiding",
    "idbg",
    "if",
    "import",
    "in",
    "include",
    "include_str",
    "inductive",
    "inductive_fixpoint",
    "inferInstanceAs",
    "infix",
    "infixl",
    "infixr",
    "init_grind_norm",
    "init_quot",
    "initialize",
    "instance",
    "leading_parser",
    "let",
    "letI",
    "let_delayed",
    "let_expr",
    "let_fun",
    "let_tmp",
    "local",
    "logNamedError",
    "logNamedErrorAt",
    "logNamedWarning",
    "logNamedWarningAt",
    "m!",
    "macro",
    "macro_rules",
    "match",
    "match_expr",
    "matches",
    "max_prec",
    "meta",
    "mod_cast",
    "mut",
    "mutual",
    "namespace",
    "nat_lit",
    "no_index",
    "nofun",
    "nomatch",
    "noncomputable",
    "nonrec",
    "norm_cast_add_elim",
    "notation",
    "omit",
    "opaque",
    "open",
    "panic!",
    "partial",
    "partial_fixpoint",
    "postfix",
    "prefix",
    "println!",
    "private",
    "protected",
    "public",
    "recommended_spelling",
    "register_builtin_option",
    "register_error_explanation",
    "register_grind_attr",
    "register_label_attr",
    "register_linter_set",
    "register_option",
    "register_parser_alias",
    "register_simp_attr",
    "register_sym_dsimp",
    "register_sym_simp",
    "register_sym_simp_attr",
    "register_tactic_tag",
    "register_try?_tactic",
    "renaming",
    "repeat",
    "reportDbgIssue!",
    "reportEMatchIssue!",
    "reportIssue!",
    "reprove",
    "return",
    "run_cmd",
    "run_elab",
    "run_meta",
    "s!",
    "scoped",
    "seal",
    "section",
    "set_library_suggestions",
    "set_option",
    "show",
    "show_panel_widgets",
    "show_term",
    "show_term_elab",
    "simproc",
    "simproc_decl",
    "sorry",
    "structure",
    "suffices",
    "syntax",
    "tactic_alt",
    "tactic_extension",
    "tactic_name",
    "tactic_tag",
    "termination_by",
    "termination_by?",
    "test_extern",
    "then",
    "theorem",
    "throwError",
    "throwErrorAt",
    "throwNamedError",
    "throwNamedErrorAt",
    "trailing_parser",
    "try",
    "unif_hint",
    "universe",
    "unless",
    "unlock_limits",
    "unreachable!",
    "unsafe",
    "unseal",
    "until",
    "using",
    "using!",
    "variable",
    "where",
    "while",
    "with",
    "with_weak_namespace",
    "without_expected_type",
];

/// The members of [`LEAN_RESERVED_TOKENS`] that only the `Std` and `Lean`
/// token tables contribute: a module importing `Init` alone parses them as
/// identifiers. They stay reserved because a generated module may import
/// any toolchain module, and the linker cannot know which tokens a later
/// import activates.
pub const RESERVED_ONLY_WITH_STD_OR_LEAN: &[&str] = &[
    "declare_command_config_elab",
    "declare_command_config_elab_legacy",
    "declare_config_elab",
    "declare_config_elab_legacy",
    "declare_core_config_elab",
    "declare_eval_bin",
    "declare_eval_bin_bitwise",
    "declare_eval_bin_bool_pred",
    "declare_sint_simprocs",
    "declare_term_config_elab",
    "declare_uint_simprocs",
    "def_eval_config_item",
    "elab_stx_quot",
    "m!",
    "register_builtin_option",
    "register_grind_attr",
    "register_label_attr",
    "register_linter_set",
    "register_option",
    "register_parser_alias",
    "register_simp_attr",
    "register_sym_simp_attr",
    "reportDbgIssue!",
    "reportEMatchIssue!",
    "reportIssue!",
    "reprove",
    "show_panel_widgets",
    "test_extern",
    "throwError",
    "throwErrorAt",
];

/// Is `name` a reserved token of the pinned toolchain?
#[must_use]
pub fn is_reserved(name: &str) -> bool {
    LEAN_RESERVED_TOKENS.binary_search(&name).is_ok()
}

#[cfg(test)]
mod tests {
    use super::{is_reserved, LEAN_RESERVED_TOKENS, RESERVED_ONLY_WITH_STD_OR_LEAN};

    /// Names Lean's tactic category declares as non-reserved symbols: legal
    /// declaration names, and the control group of the toolchain probe.
    const PLAIN_IDENTIFIERS: [&str; 12] = [
        "simp",
        "exact",
        "rw",
        "intro",
        "cases",
        "induction",
        "apply",
        "left",
        "first",
        "omega",
        "Nat_x",
        "forall_x",
    ];

    /// The list is sorted and duplicate-free, so `is_reserved` may search
    /// it binarily; the tokens the hand-written list used to miss are
    /// present and tactic names are not.
    #[test]
    fn reserved_tokens_are_sorted_and_unique() {
        for list in [LEAN_RESERVED_TOKENS, RESERVED_ONLY_WITH_STD_OR_LEAN] {
            for pair in list.windows(2) {
                assert!(pair[0] < pair[1], "`{}` precedes `{}`", pair[0], pair[1]);
            }
        }
        for token in RESERVED_ONLY_WITH_STD_OR_LEAN {
            assert!(is_reserved(token), "`{token}` is in the union list");
        }
        for token in [
            "forall",
            "meta",
            "nonrec",
            "until",
            "while",
            "seal",
            "unseal",
            "matches",
            "bif",
            "initialize",
            "simproc",
            "generalizing",
            "at",
            "calc",
            "with",
            "where",
            "then",
            "let",
            "instance",
            "exists",
            "using",
        ] {
            assert!(is_reserved(token), "`{token}` is a pinned reserved token");
        }
        for name in PLAIN_IDENTIFIERS {
            assert!(!is_reserved(name), "`{name}` is a plain identifier");
        }
    }

    /// The executable form of the derivation, when the pinned toolchain is
    /// installed, over the `Init` token table (the prelude every generated
    /// module imports; loading `Std` and `Lean` is too slow for a unit
    /// test): one `def <token> : Nat := 0` per listed token is refused by
    /// `lean` with a parse error on exactly that line, the tokens only
    /// `Std`/`Lean` contribute are accepted under `Init` alone, and so is
    /// the control group of non-reserved names.
    #[test]
    fn reserved_tokens_match_the_pinned_toolchain() {
        let Ok(root) = crate::verify::toolchain::toolchain_root() else {
            return;
        };
        let lean = root.join("bin").join("lean");
        if !lean.as_std_path().is_file() {
            return;
        }
        let (init_tokens, later_tokens): (Vec<&str>, Vec<&str>) = LEAN_RESERVED_TOKENS
            .iter()
            .partition(|token| RESERVED_ONLY_WITH_STD_OR_LEAN.binary_search(token).is_err());
        let accepted: Vec<&str> = later_tokens
            .iter()
            .copied()
            .chain(PLAIN_IDENTIFIERS)
            .collect();
        let mut source = String::from("namespace LexLeanTokenProbe\n");
        for token in &init_tokens {
            source.push_str(&format!("def {token} : Nat := 0\n"));
        }
        for name in &accepted {
            source.push_str(&format!("def {name} : Nat := 0\n"));
        }
        source.push_str("end LexLeanTokenProbe\n");
        let dir = tempfile::Builder::new()
            .prefix("lexlean-tokens-")
            .tempdir()
            .expect("tempdir");
        let path = dir.path().join("Tokens.lean");
        std::fs::write(&path, &source).expect("write probe");
        let output = std::process::Command::new(lean.as_std_path())
            .arg("-DmaxErrors=0")
            .arg(&path)
            .current_dir(dir.path())
            .env("LEAN_PATH", "")
            .output()
            .expect("the pinned lean runs");
        let text = String::from_utf8_lossy(&output.stdout).into_owned()
            + &String::from_utf8_lossy(&output.stderr);
        let error_lines: std::collections::BTreeSet<usize> =
            crate::verify::parse_lean_messages(&text)
                .iter()
                .filter(|message| message.severity == "error")
                .map(|message| message.line)
                .collect();
        for (index, token) in init_tokens.iter().enumerate() {
            let line = index + 2;
            assert!(
                error_lines.contains(&line),
                "`{token}` (line {line}) must be refused as a declaration name; lean said:\n{text}"
            );
        }
        for (index, name) in accepted.iter().enumerate() {
            let line = init_tokens.len() + index + 2;
            assert!(
                !error_lines.contains(&line),
                "`{name}` (line {line}) is a plain identifier; lean said:\n{text}"
            );
        }
    }
}
