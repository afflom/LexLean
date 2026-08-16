//! The fixed structural grammar (SPEC.md §15.1, §15.2): environments,
//! controls, headers, blocks, and the structured proof environments, parsed
//! from the primitive atom stream.

use crate::code;
use crate::diagnostic::Diagnostic;
use crate::ir::declaration::DeclKind;
use crate::source::atom::{Atom, AtomClass};

/// An inclusive-start, exclusive-end atom range.
pub type AtomRange = (usize, usize);

/// One brace-enclosed argument: the inner atom range plus its joined
/// non-whitespace text (for metadata interpretation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BraceArg {
    /// The inner atom range.
    pub range: AtomRange,
    /// The concatenated non-whitespace atom text.
    pub text: String,
}

/// One sentence: the atom range before the terminating period, and the
/// period's atom index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SentenceAst {
    /// The content range.
    pub range: AtomRange,
    /// The terminating period atom.
    pub period: usize,
}

/// An axiom policy as written (§15.9).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolicyAst {
    /// `noaxioms`, `allowaxioms`, or `exactaxioms`.
    pub kind: PolicyKind,
    /// The listed Lean names, sorted; empty for `noaxioms`.
    pub names: Vec<String>,
    /// The policy control atom.
    pub control: usize,
    /// The name-list argument, when present.
    pub names_arg: Option<BraceArg>,
}

/// The three policy kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PolicyKind {
    /// `\noaxioms`.
    None,
    /// `\allowaxioms`.
    Allow,
    /// `\exactaxioms`.
    Exact,
}

/// One structured or simple proof item, structurally parsed (§16).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofItemAst {
    /// A simple proof sentence.
    Sentence(SentenceAst),
    /// `have` (§16.3).
    Have {
        /// The hypothesis spelling.
        name: BraceArg,
        /// The established proposition sentence.
        proposition: SentenceAst,
        /// The nested proof.
        proof: ProofEnvAst,
        /// The `\begin` atom, for spans.
        begin: usize,
    },
    /// `rewrite` (§16.4).
    Rewrite {
        /// `goal` or a proof-local spelling.
        target: BraceArg,
        /// `(reverse, proof-term range)` rules in source order.
        rules: Vec<(bool, BraceArg)>,
        /// The `\begin` atom, for spans.
        begin: usize,
    },
    /// `simplify` (§16.5).
    Simplify {
        /// `goal` or a proof-local spelling.
        target: BraceArg,
        /// The listed rules in source order.
        rules: Vec<BraceArg>,
        /// The `\begin` atom, for spans.
        begin: usize,
    },
    /// Structured `apply` (§16.6).
    Apply {
        /// The applied proof term.
        function: BraceArg,
        /// `(label, premise proof)` in source order.
        premises: Vec<(u64, ProofEnvAst)>,
        /// The `\begin` atom, for spans.
        begin: usize,
    },
    /// `constructor` (§16.7).
    Constructor {
        /// `(label, branch proof)` in source order.
        branches: Vec<(u64, ProofEnvAst)>,
        /// The `\begin` atom, for spans.
        begin: usize,
    },
    /// `cases` or `induction` (§16.8, §16.9).
    CasesLike {
        /// `true` for induction.
        induction: bool,
        /// The scrutinee term range.
        scrutinee: BraceArg,
        /// The case branches in source order.
        cases: Vec<CaseAst>,
        /// The `\begin` atom, for spans.
        begin: usize,
    },
    /// `calculate` (§16.10).
    Calculate {
        /// The starting term.
        start: BraceArg,
        /// The steps in source order.
        steps: Vec<CalcStepAst>,
        /// The `\begin` atom, for spans.
        begin: usize,
    },
}

impl ProofItemAst {
    /// The atom range that locates this item in diagnostics: the sentence
    /// content, or the `\begin` control of a structured environment.
    #[must_use]
    pub fn span_atoms(&self) -> AtomRange {
        match self {
            Self::Sentence(sentence) => (sentence.range.0, sentence.period + 1),
            Self::Have { begin, .. }
            | Self::Rewrite { begin, .. }
            | Self::Simplify { begin, .. }
            | Self::Apply { begin, .. }
            | Self::Constructor { begin, .. }
            | Self::CasesLike { begin, .. }
            | Self::Calculate { begin, .. } => (*begin, *begin + 1),
        }
    }
}

/// One `case` branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseAst {
    /// The qualified constructor entry.
    pub entry: BraceArg,
    /// The `\bind{...}` spellings, possibly empty.
    pub binds: Vec<String>,
    /// The bind argument, for spans.
    pub bind_arg: BraceArg,
    /// The branch proof.
    pub proof: ProofEnvAst,
}

/// One `\step{relation}{term}{proof}`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CalcStepAst {
    /// The qualified relation entry.
    pub relation: BraceArg,
    /// The next term.
    pub term: BraceArg,
    /// The step proof term.
    pub proof: BraceArg,
}

/// A proof environment body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofEnvAst {
    /// The items in source order. Never empty for an accepted proof
    /// (§16.12); emptiness is rejected during proof elaboration so the
    /// diagnostic lands in the proof family.
    pub items: Vec<ProofItemAst>,
    /// The atom index of `\begin{proof}` (or the enclosing branch), for
    /// spans.
    pub begin: usize,
}

/// One declaration environment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclAst {
    /// The declaration kind.
    pub kind: DeclKind,
    /// The component ID argument.
    pub component: BraceArg,
    /// The qualified entry argument, for definitions.
    pub entry: Option<BraceArg>,
    /// The one axiom policy.
    pub policy: PolicyAst,
    /// The one definition or proposition sentence.
    pub sentence: SentenceAst,
    /// The one proof, exactly when theorem-like.
    pub proof: Option<ProofEnvAst>,
    /// The `\begin` atom of the environment, for spans.
    pub begin: usize,
    /// The atom index just past `\end{...}`, for spans.
    pub end: usize,
}

/// One block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockAst {
    /// A section.
    Section {
        /// The component ID argument.
        component: BraceArg,
        /// The heading phrase range.
        heading: AtomRange,
        /// The optional `\parameters{...}` range.
        params: Option<AtomRange>,
        /// Nested blocks.
        blocks: Vec<BlockAst>,
        /// The `\begin` atom, for spans.
        begin: usize,
    },
    /// A declaration.
    Declaration(DeclAst),
}

/// One parsed module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleAst {
    /// Coverage rows for every structural atom the parser consumed:
    /// controls, braces, environment names, and metadata (I1, I2, §12.3).
    pub structural_rows: Vec<crate::source::coverage::SourceRow>,
    /// The declared module name.
    pub name: String,
    /// The name argument, for spans.
    pub name_arg: BraceArg,
    /// `\useglossary` rows in source order.
    pub uses: Vec<BraceArg>,
    /// `\importmodule` rows in source order.
    pub imports: Vec<BraceArg>,
    /// The title phrase range.
    pub title: AtomRange,
    /// Top-level blocks in source order.
    pub blocks: Vec<BlockAst>,
}

struct Parser<'a> {
    path: &'a str,
    atoms: &'a [Atom],
    at: usize,
    max_scope_depth: u64,
    rows: Vec<crate::source::coverage::SourceRow>,
}

/// The covering core entry for each structural control (§15.2).
fn control_entry(name: &str) -> &'static str {
    match name {
        "\\begin" => "begin",
        "\\end" => "end",
        "\\useglossary" => "useglossary",
        "\\importmodule" => "importmodule",
        "\\title" => "title",
        "\\heading" => "heading",
        "\\parameters" => "parameters",
        "\\noaxioms" => "noaxioms",
        "\\allowaxioms" => "allowaxioms",
        "\\exactaxioms" => "exactaxioms",
        "\\lexeme" => "lexeme",
        "\\reference" => "reference",
        "\\forward" => "forward",
        "\\backward" => "backward",
        "\\rule" => "rule",
        "\\start" => "start",
        "\\step" => "step",
        "\\bind" => "bind",
        "\\(" => "math-open",
        "\\)" => "math-close",
        "\\[" => "display-open",
        "\\]" => "display-close",
        _ => "begin",
    }
}

type PResult<T> = Result<T, Diagnostic>;

impl<'a> Parser<'a> {
    fn cover(&mut self, index: usize, binding: crate::source::coverage::Origin) {
        let atom = &self.atoms[index];
        self.rows.push(crate::source::coverage::SourceRow {
            path: self.path.to_owned(),
            byte_start: atom.byte_start,
            byte_end: atom.byte_end,
            class: atom.class,
            binding,
        });
    }

    fn cover_structural(&mut self, index: usize, entry: &str) {
        self.cover(
            index,
            crate::source::coverage::Origin::Structural {
                package: "lexlean.core".to_owned(),
                entry: entry.to_owned(),
            },
        );
    }

    /// Cover every non-whitespace atom of a metadata argument, braces
    /// included by the caller through `brace_arg`.
    fn cover_metadata(&mut self, range: AtomRange, owner: &str) {
        for index in range.0..range.1 {
            if self.atoms[index].class == AtomClass::Whitespace {
                continue;
            }
            self.cover(
                index,
                crate::source::coverage::Origin::Metadata {
                    owner: format!("lexlean.core::{owner}"),
                },
            );
        }
    }

    /// Cover an environment-name argument.
    fn cover_env_name(&mut self, range: AtomRange, name: &str) {
        for index in range.0..range.1 {
            if self.atoms[index].class == AtomClass::Whitespace {
                continue;
            }
            self.cover(
                index,
                crate::source::coverage::Origin::Structural {
                    package: "lexlean.core".to_owned(),
                    entry: format!("env.{name}"),
                },
            );
        }
    }

    fn skip_ws(&mut self) {
        while self
            .atoms
            .get(self.at)
            .is_some_and(|atom| atom.class == AtomClass::Whitespace)
        {
            self.at += 1;
        }
    }

    fn peek(&mut self) -> Option<&'a Atom> {
        self.skip_ws();
        self.atoms.get(self.at)
    }

    fn here_span(&mut self) -> crate::diagnostic::Span {
        self.skip_ws();
        match self
            .atoms
            .get(self.at.min(self.atoms.len().saturating_sub(1)))
        {
            Some(atom) => atom.span(self.path),
            None => crate::diagnostic::Span::whole_file(self.path),
        }
    }

    fn fail(&mut self, code: crate::diagnostic::DiagnosticCode, message: String) -> Diagnostic {
        let span = self.here_span();
        Diagnostic::new(code, message).with_span(span)
    }

    fn expect_control(&mut self, name: &str) -> PResult<usize> {
        match self.peek() {
            Some(atom) if atom.class == AtomClass::Control && atom.text == name => {
                let index = self.at;
                self.at += 1;
                self.cover_structural(index, control_entry(name));
                Ok(index)
            }
            Some(atom) => Err(self.fail(
                code!("LLP2003"),
                format!("expected `{name}`, found `{}`", atom.text),
            )),
            None => Err(self.fail(
                code!("LLP2003"),
                format!("expected `{name}`, found end of file"),
            )),
        }
    }

    fn expect_delim(&mut self, text: &str) -> PResult<usize> {
        match self.peek() {
            Some(atom) if atom.class == AtomClass::Delimiter && atom.text == text => {
                let index = self.at;
                self.at += 1;
                if text == "{" {
                    self.cover_structural(index, "brace-open");
                } else if text == "}" {
                    self.cover_structural(index, "brace-close");
                }
                Ok(index)
            }
            Some(atom) => Err(self.fail(
                code!("LLP2003"),
                format!("expected `{text}`, found `{}`", atom.text),
            )),
            None => Err(self.fail(
                code!("LLP2003"),
                format!("expected `{text}`, found end of file"),
            )),
        }
    }

    /// Capture one `{ ... }` argument with balanced inner braces.
    fn brace_arg(&mut self) -> PResult<BraceArg> {
        self.expect_delim("{")?;
        let start = self.at;
        let mut depth = 0usize;
        let mut text = String::new();
        loop {
            let Some(atom) = self.atoms.get(self.at) else {
                return Err(self.fail(code!("LLP2003"), "unclosed `{` argument".to_owned()));
            };
            match (atom.class, atom.text.as_str()) {
                (AtomClass::Delimiter, "{") => {
                    depth += 1;
                    text.push('{');
                }
                (AtomClass::Delimiter, "}") => {
                    if depth == 0 {
                        let end = self.at;
                        self.at += 1;
                        self.cover_structural(end, "brace-close");
                        return Ok(BraceArg {
                            range: (start, end),
                            text,
                        });
                    }
                    depth -= 1;
                    text.push('}');
                }
                (AtomClass::Whitespace, _) => {}
                _ => text.push_str(&atom.text),
            }
            self.at += 1;
        }
    }

    /// `\begin{name}`; returns the `\begin` atom index and the name.
    fn begin_env(&mut self) -> PResult<(usize, String)> {
        let begin = self.expect_control("\\begin")?;
        let name = self.brace_arg()?;
        self.cover_env_name(name.range, &name.text);
        Ok((begin, name.text))
    }

    fn expect_end(&mut self, name: &str) -> PResult<()> {
        self.expect_control("\\end")?;
        let arg = self.brace_arg()?;
        if arg.text == name {
            self.cover_env_name(arg.range, name);
            Ok(())
        } else {
            Err(self.fail(
                code!("LLP2003"),
                format!("expected `\\end{{{name}}}`, found `\\end{{{}}}`", arg.text),
            ))
        }
    }

    fn at_control(&mut self, name: &str) -> bool {
        matches!(self.peek(), Some(atom) if atom.class == AtomClass::Control && atom.text == name)
    }

    fn at_begin_of(&mut self, name: &str) -> bool {
        if !self.at_control("\\begin") {
            return false;
        }
        // Look ahead without consuming: `\begin` `{` name `}`.
        let mut scan = self.at + 1;
        let mut next = |expect_ws_ok: bool| -> Option<&'a Atom> {
            while self
                .atoms
                .get(scan)
                .is_some_and(|atom| expect_ws_ok && atom.class == AtomClass::Whitespace)
            {
                scan += 1;
            }
            let atom = self.atoms.get(scan);
            scan += 1;
            atom
        };
        matches!(next(true), Some(a) if a.class == AtomClass::Delimiter && a.text == "{")
            && matches!(next(false), Some(a) if a.text == name)
            && matches!(next(false), Some(a) if a.class == AtomClass::Delimiter && a.text == "}")
    }

    /// Capture a sentence: content up to the first `.` at brace depth zero
    /// outside math islands.
    fn sentence(&mut self) -> PResult<SentenceAst> {
        self.skip_ws();
        let start = self.at;
        let mut depth = 0usize;
        let mut island: Option<&str> = None;
        loop {
            let Some(atom) = self.atoms.get(self.at) else {
                return Err(self.fail(
                    code!("LLP2001"),
                    "a sentence must end with a period".to_owned(),
                ));
            };
            match (atom.class, atom.text.as_str()) {
                (AtomClass::Control, "\\(") if island.is_none() => island = Some("\\)"),
                (AtomClass::Control, "\\[") if island.is_none() => island = Some("\\]"),
                (AtomClass::Control, closer) if island == Some(closer) => island = None,
                (AtomClass::Control, "\\begin" | "\\end") if island.is_none() && depth == 0 => {
                    return Err(self.fail(
                        code!("LLP2001"),
                        "a sentence must end with a period".to_owned(),
                    ));
                }
                (AtomClass::Delimiter, "{") if island.is_none() => depth += 1,
                (AtomClass::Delimiter, "}") if island.is_none() => {
                    depth = depth.saturating_sub(1);
                }
                (AtomClass::AsciiSymbol, ".") if island.is_none() && depth == 0 => {
                    let period = self.at;
                    self.at += 1;
                    return Ok(SentenceAst {
                        range: (start, period),
                        period,
                    });
                }
                _ => {}
            }
            self.at += 1;
        }
    }

    fn lean_name_list(&mut self, arg: &BraceArg) -> PResult<Vec<String>> {
        let mut names: Vec<String> = Vec::new();
        for piece in arg.text.split(';') {
            if piece.is_empty() {
                return Err(self.fail(
                    code!("LLP2003"),
                    "empty entry in an axiom name list".to_owned(),
                ));
            }
            if !crate::lexicon::entry::is_lean_name(piece) {
                return Err(self.fail(
                    code!("LLP2003"),
                    format!("`{piece}` is not a conservative ASCII Lean name"),
                ));
            }
            if names.contains(&piece.to_owned()) {
                return Err(self.fail(code!("LLP2003"), format!("duplicate axiom name `{piece}`")));
            }
            names.push(piece.to_owned());
        }
        names.sort();
        Ok(names)
    }

    fn policy(&mut self) -> PResult<PolicyAst> {
        let (kind, control) = if self.at_control("\\noaxioms") {
            (PolicyKind::None, self.expect_control("\\noaxioms")?)
        } else if self.at_control("\\allowaxioms") {
            (PolicyKind::Allow, self.expect_control("\\allowaxioms")?)
        } else if self.at_control("\\exactaxioms") {
            (PolicyKind::Exact, self.expect_control("\\exactaxioms")?)
        } else {
            return Err(self.fail(
                code!("LLP2003"),
                "every definition and theorem-like declaration requires exactly one axiom policy"
                    .to_owned(),
            ));
        };
        if matches!(kind, PolicyKind::None) {
            return Ok(PolicyAst {
                kind,
                names: Vec::new(),
                control,
                names_arg: None,
            });
        }
        let arg = self.brace_arg()?;
        self.cover_metadata(
            arg.range,
            if matches!(kind, PolicyKind::Allow) {
                "allowaxioms"
            } else {
                "exactaxioms"
            },
        );
        let names = self.lean_name_list(&arg)?;
        if names.is_empty() {
            return Err(self.fail(
                code!("LLP2003"),
                "an allow or exact policy lists at least one axiom".to_owned(),
            ));
        }
        Ok(PolicyAst {
            kind,
            names,
            control,
            names_arg: Some(arg),
        })
    }

    fn decimal_arg(&mut self, arg: &BraceArg) -> PResult<u64> {
        arg.text.parse::<u64>().map_err(|_| {
            self.fail(
                code!("LLP2003"),
                format!("`{}` is not a decimal label", arg.text),
            )
        })
    }

    /// A proof body: items until the matching `\end{...}` of `env_name`.
    /// `depth` counts nested proof environments against `max_scope_depth`
    /// (§25.5).
    fn proof_body(&mut self, begin: usize, env_name: &str, depth: u64) -> PResult<ProofEnvAst> {
        if let Err(diagnostic) =
            crate::grammar::chart::depth_check(depth, self.max_scope_depth, "parse (proof environment nesting)")
        {
            let span = self.here_span();
            return Err(diagnostic.with_span(span));
        }
        let mut items = Vec::new();
        loop {
            self.skip_ws();
            if self.at_control("\\end") {
                self.expect_end(env_name)?;
                return Ok(ProofEnvAst { items, begin });
            }
            if self.at_control("\\begin") {
                items.push(self.proof_env_item(depth)?);
            } else if self.peek().is_none() {
                return Err(self.fail(
                    code!("LLP2003"),
                    format!("unclosed `{env_name}` environment"),
                ));
            } else {
                items.push(ProofItemAst::Sentence(self.sentence()?));
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn proof_env_item(&mut self, depth: u64) -> PResult<ProofItemAst> {
        let (begin, name) = self.begin_env()?;
        let nested = depth.saturating_add(1);
        match name.as_str() {
            "have" => {
                let hypothesis = self.brace_arg()?;
                self.cover_metadata(hypothesis.range, "env.have");
                let proposition = self.sentence()?;
                let (proof_begin, proof_name) = self.begin_env()?;
                if proof_name != "proof" {
                    return Err(self.fail(
                        code!("LLP2003"),
                        "a have establishes its proposition with a nested proof".to_owned(),
                    ));
                }
                let proof = self.proof_body(proof_begin, "proof", nested)?;
                self.expect_end("have")?;
                Ok(ProofItemAst::Have {
                    name: hypothesis,
                    proposition,
                    proof,
                    begin,
                })
            }
            "rewrite" => {
                let target = self.brace_arg()?;
                self.cover_metadata(target.range, "env.rewrite");
                let mut rules = Vec::new();
                loop {
                    if self.at_control("\\forward") {
                        self.expect_control("\\forward")?;
                        rules.push((false, self.brace_arg()?));
                    } else if self.at_control("\\backward") {
                        self.expect_control("\\backward")?;
                        rules.push((true, self.brace_arg()?));
                    } else {
                        break;
                    }
                }
                self.expect_end("rewrite")?;
                if rules.is_empty() {
                    return Err(self.fail(
                        code!("LLF5003"),
                        "a rewrite requires at least one rule".to_owned(),
                    ));
                }
                Ok(ProofItemAst::Rewrite {
                    target,
                    rules,
                    begin,
                })
            }
            "simplify" => {
                let target = self.brace_arg()?;
                self.cover_metadata(target.range, "env.simplify");
                let mut rules = Vec::new();
                while self.at_control("\\rule") {
                    self.expect_control("\\rule")?;
                    rules.push(self.brace_arg()?);
                }
                self.expect_end("simplify")?;
                if rules.is_empty() {
                    return Err(self.fail(
                        code!("LLF5003"),
                        "a simplify requires at least one rule".to_owned(),
                    ));
                }
                Ok(ProofItemAst::Simplify {
                    target,
                    rules,
                    begin,
                })
            }
            "apply" => {
                let function = self.brace_arg()?;
                let mut premises = Vec::new();
                while self.at_begin_of("premise") {
                    let (premise_begin, _) = self.begin_env()?;
                    let label_arg = self.brace_arg()?;
                    self.cover_metadata(label_arg.range, "env.premise");
                    let label = self.decimal_arg(&label_arg)?;
                    let body = self.proof_body(premise_begin, "premise", nested)?;
                    premises.push((label, body));
                }
                self.expect_end("apply")?;
                Ok(ProofItemAst::Apply {
                    function,
                    premises,
                    begin,
                })
            }
            "constructor" => {
                let mut branches = Vec::new();
                while self.at_begin_of("branch") {
                    let (branch_begin, _) = self.begin_env()?;
                    let label_arg = self.brace_arg()?;
                    self.cover_metadata(label_arg.range, "env.branch");
                    let label = self.decimal_arg(&label_arg)?;
                    let body = self.proof_body(branch_begin, "branch", nested)?;
                    branches.push((label, body));
                }
                self.expect_end("constructor")?;
                Ok(ProofItemAst::Constructor { branches, begin })
            }
            kind @ ("cases" | "induction") => {
                let induction = kind == "induction";
                let scrutinee = self.brace_arg()?;
                let mut cases = Vec::new();
                while self.at_begin_of("case") {
                    let (case_begin, _) = self.begin_env()?;
                    let entry = self.brace_arg()?;
                    self.cover_metadata(entry.range, "env.case");
                    self.expect_control("\\bind")?;
                    let bind_arg = self.brace_arg()?;
                    self.cover_metadata(bind_arg.range, "bind");
                    let binds: Vec<String> = if bind_arg.text.is_empty() {
                        Vec::new()
                    } else {
                        bind_arg.text.split(';').map(str::to_owned).collect()
                    };
                    let body = self.proof_body(case_begin, "case", nested)?;
                    cases.push(CaseAst {
                        entry,
                        binds,
                        bind_arg,
                        proof: body,
                    });
                }
                self.expect_end(kind)?;
                Ok(ProofItemAst::CasesLike {
                    induction,
                    scrutinee,
                    cases,
                    begin,
                })
            }
            "calculate" => {
                self.expect_control("\\start")?;
                let start = self.brace_arg()?;
                let mut steps = Vec::new();
                while self.at_control("\\step") {
                    self.expect_control("\\step")?;
                    let relation = self.brace_arg()?;
                    self.cover_metadata(relation.range, "step");
                    let term = self.brace_arg()?;
                    let proof = self.brace_arg()?;
                    steps.push(CalcStepAst {
                        relation,
                        term,
                        proof,
                    });
                }
                self.expect_end("calculate")?;
                if steps.is_empty() {
                    return Err(self.fail(
                        code!("LLF5003"),
                        "a calculation requires at least one step".to_owned(),
                    ));
                }
                Ok(ProofItemAst::Calculate {
                    start,
                    steps,
                    begin,
                })
            }
            other => Err(self.fail(
                code!("LLL1004"),
                format!("`{other}` is not a proof environment"),
            )),
        }
    }

    fn declaration(&mut self, begin: usize, env: &str) -> PResult<DeclAst> {
        let kind = match env {
            "typedefinition" => DeclKind::TypeDefinition,
            "termdefinition" => DeclKind::TermDefinition,
            "predicatedefinition" => DeclKind::PredicateDefinition,
            "theorem" => DeclKind::Theorem,
            "lemma" => DeclKind::Lemma,
            "corollary" => DeclKind::Corollary,
            _ => unreachable!("caller dispatches on the environment set"),
        };
        let component = self.brace_arg()?;
        if !is_component_id(&component.text) {
            return Err(self.fail(
                code!("LLP2003"),
                format!("`{}` is not a component ID", component.text),
            ));
        }
        self.cover_metadata(component.range, &format!("env.{env}"));
        let entry = if kind.is_theorem_like() {
            None
        } else {
            let entry_arg = self.brace_arg()?;
            self.cover_metadata(entry_arg.range, &format!("env.{env}"));
            Some(entry_arg)
        };
        let policy = self.policy()?;
        let sentence = self.sentence()?;
        let proof = if kind.is_theorem_like() {
            if !self.at_begin_of("proof") {
                return Err(self.fail(
                    code!("LLF5005"),
                    "a theorem-like declaration without a proof is not valid".to_owned(),
                ));
            }
            let (proof_begin, _) = self.begin_env()?;
            Some(self.proof_body(proof_begin, "proof", 1)?)
        } else {
            if self.at_begin_of("proof") {
                return Err(self.fail(
                    code!("LLP2003"),
                    "no definitional component accepts a proof environment".to_owned(),
                ));
            }
            None
        };
        self.expect_end(env)?;
        Ok(DeclAst {
            kind,
            component,
            entry,
            policy,
            sentence,
            proof,
            begin,
            end: self.at,
        })
    }

    fn blocks(&mut self, terminator: &str, depth: u64) -> PResult<Vec<BlockAst>> {
        let mut blocks = Vec::new();
        loop {
            self.skip_ws();
            if self.at_control("\\end") {
                self.expect_end(terminator)?;
                return Ok(blocks);
            }
            if !self.at_control("\\begin") {
                return match self.peek() {
                    Some(atom) => Err(self.fail(
                        code!("LLP2003"),
                        format!(
                            "expected a block or `\\end{{{terminator}}}`, found `{}`",
                            atom.text
                        ),
                    )),
                    None => Err(self.fail(
                        code!("LLP2003"),
                        format!("unclosed `{terminator}` environment"),
                    )),
                };
            }
            let (begin, env) = self.begin_env()?;
            match env.as_str() {
                "section" => {
                    if depth + 1 > self.max_scope_depth {
                        return Err(self.fail(
                            code!("LLS8002"),
                            format!(
                                "max_scope_depth exceeded: configured {}",
                                self.max_scope_depth
                            ),
                        ));
                    }
                    let component = self.brace_arg()?;
                    if !is_component_id(&component.text) {
                        return Err(self.fail(
                            code!("LLP2003"),
                            format!("`{}` is not a component ID", component.text),
                        ));
                    }
                    self.cover_metadata(component.range, "env.section");
                    self.expect_control("\\heading")?;
                    let heading = self.brace_arg()?;
                    let params = if self.at_control("\\parameters") {
                        self.expect_control("\\parameters")?;
                        Some(self.brace_arg()?.range)
                    } else {
                        None
                    };
                    let inner = self.blocks("section", depth + 1)?;
                    blocks.push(BlockAst::Section {
                        component,
                        heading: heading.range,
                        params,
                        blocks: inner,
                        begin,
                    });
                }
                "typedefinition"
                | "termdefinition"
                | "predicatedefinition"
                | "theorem"
                | "lemma"
                | "corollary" => {
                    blocks.push(BlockAst::Declaration(self.declaration(begin, &env)?));
                }
                other => {
                    return Err(self.fail(
                        code!("LLL1004"),
                        format!("`{other}` is not a block environment"),
                    ));
                }
            }
        }
    }
}

/// `[a-z][a-z0-9-]*` (§15.1).
#[must_use]
pub fn is_component_id(text: &str) -> bool {
    let bytes = text.as_bytes();
    matches!(bytes.first(), Some(b) if b.is_ascii_lowercase())
        && bytes[1..]
            .iter()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || *b == b'-')
}

/// Parse one module (§15.1). `expected_name` is the module name derived
/// from the source path; the declared name must match it.
pub fn parse_module(
    path: &str,
    atoms: &[Atom],
    expected_name: &str,
    max_scope_depth: u64,
) -> Result<ModuleAst, Diagnostic> {
    let mut parser = Parser {
        path,
        atoms,
        at: 0,
        max_scope_depth,
        rows: Vec::new(),
    };
    let (_, env) = parser.begin_env()?;
    if env != "lexlean" {
        return Err(parser.fail(
            code!("LLP2003"),
            "a module begins with \\begin{lexlean}{module-name}".to_owned(),
        ));
    }
    let name_arg = parser.brace_arg()?;
    parser.cover_metadata(name_arg.range, "env.lexlean");
    if name_arg.text != expected_name {
        return Err(parser.fail(
            code!("LLP2003"),
            format!(
                "the declared module `{}` does not match the source path module `{expected_name}`",
                name_arg.text
            ),
        ));
    }

    // Header: use-glossary rows, then import rows, then exactly one title
    // (§15.1, GR-02).
    let mut uses = Vec::new();
    while parser.at_control("\\useglossary") {
        parser.expect_control("\\useglossary")?;
        let use_arg = parser.brace_arg()?;
        parser.cover_metadata(use_arg.range, "useglossary");
        uses.push(use_arg);
    }
    let mut imports = Vec::new();
    while parser.at_control("\\importmodule") {
        parser.expect_control("\\importmodule")?;
        let import_arg = parser.brace_arg()?;
        parser.cover_metadata(import_arg.range, "importmodule");
        imports.push(import_arg);
    }
    if parser.at_control("\\useglossary") {
        return Err(parser.fail(
            code!("LLP2003"),
            "glossary imports occur before module imports in the header".to_owned(),
        ));
    }
    parser.expect_control("\\title")?;
    let title = parser.brace_arg()?;
    if parser.at_control("\\title") {
        return Err(parser.fail(
            code!("LLP2003"),
            "each module has exactly one title".to_owned(),
        ));
    }

    let blocks = parser.blocks("lexlean", 0)?;
    parser.skip_ws();
    if let Some(atom) = parser.peek() {
        return Err(parser.fail(
            code!("LLP2003"),
            format!("unexpected `{}` after \\end{{lexlean}}", atom.text),
        ));
    }
    Ok(ModuleAst {
        structural_rows: parser.rows,
        name: name_arg.text.clone(),
        name_arg,
        uses,
        imports,
        title: title.range,
        blocks,
    })
}
