//! Project configuration: parsing, validation, and the canonical TOML
//! serialization (SPEC.md §10).

use serde::Deserialize;

use crate::artifact::content_id::Sha256Digest;
use crate::code;
use crate::diagnostic::{Diagnostic, Span};
use crate::lexicon::lse::is_package_id;
use crate::lexicon::package::toml_comment_at;

/// The explicit resource policy (§10.2). Every limit is required and
/// positive; there are no hidden compiler defaults.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
#[allow(missing_docs)]
pub struct Limits {
    pub max_file_bytes: u64,
    pub max_total_source_bytes: u64,
    pub max_primitive_atoms: u64,
    pub max_token_lattice_edges: u64,
    pub max_parse_states: u64,
    pub max_ir_nodes: u64,
    pub max_scope_depth: u64,
    pub max_import_depth: u64,
    pub max_diagnostics: u64,
    pub max_child_output_bytes: u64,
    pub child_timeout_ms: u64,
}

/// How the compile pipeline's thread stack is sized from the configured
/// nesting limit (§25.5): the depth-independent needs of the pipeline plus
/// one measured budget per nesting level, and the deepest nesting that
/// stack can actually host.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CompileStackPlan {
    /// The stack to request for the compile thread.
    pub stack_bytes: usize,
    /// The deepest nesting the pipeline may accept on that stack.
    pub effective_max_scope_depth: u64,
}

/// The stack the pipeline needs regardless of nesting: the phases' own
/// frames, buffers, and the non-recursive work between them.
const BASE_COMPILE_STACK_BYTES: usize = 16 * 1024 * 1024;

/// The stack budget for one level of source nesting. One source level
/// recurses through the structural parser, the token-lattice chart, the
/// elaborator, the printers, and canonical serialization; measured at
/// roughly 32 KiB per level for the deepest of those paths (nested
/// mathematical grouping) in an unoptimized build, and doubled here so an
/// unoptimized build keeps a full level of margin.
const COMPILE_STACK_BYTES_PER_SCOPE: usize = 64 * 1024;

/// The largest stack LexLean will request for one compile thread. This is
/// a resource reservation, not a language limit: nesting beyond what it
/// hosts is refused as `LLS8002` naming both the configured and the
/// effective bound, never by exhausting the stack.
const MAX_COMPILE_STACK_BYTES: usize = 1024 * 1024 * 1024;

impl Limits {
    /// Size the compile thread's stack from `max_scope_depth` with checked
    /// arithmetic, and report the nesting depth that stack hosts. A
    /// configured depth too large to host is not an error here: the
    /// pipeline enforces the effective bound and reports `LLS8002` if the
    /// input actually nests that deep.
    #[must_use]
    pub fn compile_stack_plan(&self) -> CompileStackPlan {
        let requested = usize::try_from(self.max_scope_depth)
            .ok()
            .and_then(|depth| depth.checked_mul(COMPILE_STACK_BYTES_PER_SCOPE))
            .and_then(|scoped| scoped.checked_add(BASE_COMPILE_STACK_BYTES))
            .unwrap_or(usize::MAX);
        let stack_bytes = requested.min(MAX_COMPILE_STACK_BYTES);
        let hosted = (stack_bytes - BASE_COMPILE_STACK_BYTES) / COMPILE_STACK_BYTES_PER_SCOPE;
        CompileStackPlan {
            stack_bytes,
            effective_max_scope_depth: u64::try_from(hosted)
                .unwrap_or(u64::MAX)
                .min(self.max_scope_depth),
        }
    }

    /// These limits as the pipeline may enforce them on the stack it runs
    /// on: `max_scope_depth` is lowered to the depth that stack hosts when
    /// the configured value exceeds it. Every other limit is unchanged.
    #[must_use]
    pub fn within_compile_stack(self) -> Self {
        Self {
            max_scope_depth: self.compile_stack_plan().effective_max_scope_depth,
            ..self
        }
    }

    fn rows(&self) -> [(&'static str, u64); 11] {
        [
            ("max_file_bytes", self.max_file_bytes),
            ("max_total_source_bytes", self.max_total_source_bytes),
            ("max_primitive_atoms", self.max_primitive_atoms),
            ("max_token_lattice_edges", self.max_token_lattice_edges),
            ("max_parse_states", self.max_parse_states),
            ("max_ir_nodes", self.max_ir_nodes),
            ("max_scope_depth", self.max_scope_depth),
            ("max_import_depth", self.max_import_depth),
            ("max_diagnostics", self.max_diagnostics),
            ("max_child_output_bytes", self.max_child_output_bytes),
            ("child_timeout_ms", self.child_timeout_ms),
        ]
    }
}

/// One configured lexicon source (§10.1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexiconSource {
    /// An embedded builtin package.
    Builtin {
        /// The package ID.
        package: String,
    },
    /// A local path package.
    Path {
        /// The package ID.
        package: String,
        /// The project-relative package root.
        path: String,
    },
    /// An exact-commit HTTPS Git package.
    Git {
        /// The package ID.
        package: String,
        /// The HTTPS URL.
        url: String,
        /// The exact 40-lowercase-hex commit.
        revision: String,
        /// The relative subdirectory containing the package.
        subdirectory: String,
    },
}

impl LexiconSource {
    /// The configured package ID.
    #[must_use]
    pub fn package(&self) -> &str {
        match self {
            Self::Builtin { package } | Self::Path { package, .. } | Self::Git { package, .. } => {
                package
            }
        }
    }
}

/// The optional external PDF provider (§10.3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PdfProvider {
    /// The project-relative provider executable.
    pub program: String,
    /// Required SHA-256 of the executable bytes.
    pub program_sha256: Sha256Digest,
    /// The version probe argv.
    pub version_argv: Vec<String>,
    /// Required SHA-256 of the normalized version stdout.
    pub version_stdout_sha256: Sha256Digest,
    /// The compile argv with whole-argument placeholders.
    pub compile_argv: Vec<String>,
    /// The expected output file pattern containing `{stem}`.
    pub output: String,
    /// Declared regular resource files.
    pub resources: Vec<String>,
}

/// The validated project configuration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectConfig {
    /// The project name.
    pub name: String,
    /// The Lean module prefix.
    pub module_prefix: String,
    /// Sorted unique source roots.
    pub source_roots: Vec<String>,
    /// Sorted unique entrypoints.
    pub entrypoints: Vec<String>,
    /// The build root.
    pub build_root: String,
    /// The lock file path.
    pub lockfile: String,
    /// The Lake workspace directory.
    pub lean_workspace: String,
    /// Configured lexicon sources, sorted by package.
    pub lexicon_sources: Vec<LexiconSource>,
    /// The explicit resource policy.
    pub limits: Limits,
    /// The optional PDF provider.
    pub pdf: Option<PdfProvider>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawProject {
    spec: String,
    name: String,
    language: String,
    module_prefix: String,
    source_roots: Vec<String>,
    entrypoints: Vec<String>,
    build_root: String,
    lockfile: String,
    lean_workspace: String,
    lean_toolchain: String,
    #[serde(rename = "lexicon_source")]
    lexicon_sources: Vec<RawLexiconSource>,
    limits: Limits,
    pdf: Option<RawPdf>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawLexiconSource {
    package: String,
    kind: String,
    path: Option<String>,
    url: Option<String>,
    revision: Option<String>,
    subdirectory: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawPdf {
    mode: String,
    program: String,
    program_sha256: String,
    version_argv: Vec<String>,
    version_stdout_sha256: String,
    compile_argv: Vec<String>,
    output: String,
    resources: Vec<String>,
}

fn config_error(path: &str, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLC0101"), message).with_span(Span::whole_file(path))
}

/// Is `text` a project-relative path: nonempty, `/`-separated, no leading
/// separator, no `.` or `..` segments, no backslash, no NUL?
#[must_use]
pub fn is_project_relative(text: &str) -> bool {
    !text.is_empty()
        && !text.contains('\\')
        && !text.contains('\0')
        && !text.starts_with('/')
        && !text.ends_with('/')
        && text
            .split('/')
            .all(|segment| !segment.is_empty() && segment != "." && segment != "..")
}

/// Is one project-relative path equal to, inside, or containing the other?
fn path_overlaps(a: &str, b: &str) -> bool {
    a == b
        || a.strip_prefix(b).is_some_and(|rest| rest.starts_with('/'))
        || b.strip_prefix(a).is_some_and(|rest| rest.starts_with('/'))
}

/// A project name (§10.1): `[a-z][a-z0-9-]{0,62}`.
#[must_use]
pub fn is_project_name(text: &str) -> bool {
    let bytes = text.as_bytes();
    (1..=63).contains(&bytes.len())
        && bytes[0].is_ascii_lowercase()
        && bytes[1..]
            .iter()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || *b == b'-')
}

/// One `[A-Z][A-Za-z0-9_]*` Lean-name segment (§10.1).
#[must_use]
pub fn is_module_segment(text: &str) -> bool {
    let bytes = text.as_bytes();
    matches!(bytes.first(), Some(b) if b.is_ascii_uppercase())
        && bytes[1..]
            .iter()
            .all(|b| b.is_ascii_alphanumeric() || *b == b'_')
}

fn parse_hex64(path: &str, field: &str, text: &str, out: &mut Vec<Diagnostic>) -> Sha256Digest {
    match Sha256Digest::from_hex(text) {
        Ok(digest) => digest,
        Err(reason) => {
            out.push(config_error(path, format!("{field}: {reason}")));
            Sha256Digest([0; 32])
        }
    }
}

/// Parse and validate `lexlean.toml` (§10.1). `path` is the display path
/// for diagnostics.
#[allow(clippy::too_many_lines)]
pub fn parse_project(path: &str, bytes: &[u8]) -> Result<ProjectConfig, Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    let Ok(text) = std::str::from_utf8(bytes) else {
        return Err(vec![config_error(path, "lexlean.toml is not UTF-8")]);
    };
    // UTF-8, NFC, LF-terminated (§10.1): a CR anywhere, a non-NFC scalar,
    // or a missing final LF is a configuration error, not a formatting
    // suggestion.
    if text.contains('\r') {
        diagnostics.push(config_error(
            path,
            "lexlean.toml must use LF line endings; a carriage return was found",
        ));
    }
    if !unicode_normalization::is_nfc(text) {
        diagnostics.push(config_error(path, "lexlean.toml must be NFC-normalized"));
    }
    if !text.is_empty() && !text.ends_with('\n') {
        diagnostics.push(config_error(
            path,
            "lexlean.toml must end with exactly one final LF",
        ));
    }
    if let Some(at) = toml_comment_at(text) {
        diagnostics.push(config_error(
            path,
            format!("comments are forbidden (byte {at})"),
        ));
    }
    let raw: RawProject = match toml::from_str(text) {
        Ok(raw) => raw,
        Err(parse_error) => {
            diagnostics.push(config_error(
                path,
                format!("invalid project configuration: {parse_error}"),
            ));
            return Err(diagnostics);
        }
    };
    if raw.spec != "lexlean/project/1" {
        diagnostics.push(
            Diagnostic::new(
                code!("LLC0103"),
                format!("unsupported project schema `{}`", raw.spec),
            )
            .with_span(Span::whole_file(path)),
        );
    }
    if raw.language != crate::LANGUAGE_VERSION {
        diagnostics.push(
            Diagnostic::new(
                code!("LLC0103"),
                format!("unsupported language version `{}`", raw.language),
            )
            .with_span(Span::whole_file(path)),
        );
    }
    if !is_project_name(&raw.name) {
        diagnostics.push(config_error(
            path,
            format!("`{}` is not a valid project name", raw.name),
        ));
    }
    if raw.module_prefix.split('.').count() == 0
        || !raw.module_prefix.split('.').all(is_module_segment)
    {
        diagnostics.push(config_error(
            path,
            format!("`{}` is not a valid module prefix", raw.module_prefix),
        ));
    }
    if raw.lean_toolchain != crate::LEAN_TOOLCHAIN {
        diagnostics.push(config_error(
            path,
            format!("lean_toolchain must be exactly `{}`", crate::LEAN_TOOLCHAIN),
        ));
    }
    for (field, values) in [
        ("source_roots", &raw.source_roots),
        ("entrypoints", &raw.entrypoints),
    ] {
        if values.is_empty() {
            diagnostics.push(config_error(path, format!("{field} must be nonempty")));
        }
        if !values.windows(2).all(|pair| pair[0] < pair[1]) {
            diagnostics.push(config_error(
                path,
                format!("{field} must be unique and sorted"),
            ));
        }
        for value in values {
            if !is_project_relative(value) {
                diagnostics.push(config_error(
                    path,
                    format!("{field}: `{value}` is not a project-relative path"),
                ));
            }
        }
    }
    for entrypoint in &raw.entrypoints {
        if !entrypoint.ends_with(".lex.tex") {
            diagnostics.push(config_error(
                path,
                format!("entrypoint `{entrypoint}` is not a .lex.tex file"),
            ));
        } else if !raw.source_roots.iter().any(|root| {
            entrypoint
                .strip_prefix(root.as_str())
                .is_some_and(|rest| rest.starts_with('/'))
        }) {
            diagnostics.push(config_error(
                path,
                format!("entrypoint `{entrypoint}` is not beneath a source root"),
            ));
        }
    }
    for (field, value) in [("build_root", &raw.build_root), ("lockfile", &raw.lockfile)] {
        if !is_project_relative(value) {
            diagnostics.push(config_error(
                path,
                format!("{field}: `{value}` is not a project-relative path"),
            ));
        }
    }
    if raw.lean_workspace != "." && !is_project_relative(&raw.lean_workspace) {
        diagnostics.push(config_error(
            path,
            format!(
                "lean_workspace: `{}` is not a project-relative directory",
                raw.lean_workspace
            ),
        ));
    }
    // The lock file, the configuration, the entrypoints, and the build
    // root are distinct project files (§10): the lock cannot be the
    // configuration or a module, and the build root cannot contain or be
    // contained by a source root.
    if raw.lockfile == path || raw.lockfile == "lexlean.toml" {
        diagnostics.push(config_error(
            path,
            format!(
                "lockfile: `{}` is the project configuration file itself",
                raw.lockfile
            ),
        ));
    }
    if raw.entrypoints.contains(&raw.lockfile) {
        diagnostics.push(config_error(
            path,
            format!(
                "lockfile: `{}` is also a configured entrypoint",
                raw.lockfile
            ),
        ));
    }
    if raw.build_root == raw.lockfile {
        diagnostics.push(config_error(
            path,
            format!(
                "build_root: `{}` is also the configured lockfile",
                raw.build_root
            ),
        ));
    }
    if is_project_relative(&raw.build_root) {
        for root in &raw.source_roots {
            if path_overlaps(&raw.build_root, root) {
                diagnostics.push(config_error(
                    path,
                    format!(
                        "build_root `{}` and source root `{root}` overlap; the build root must be disjoint from every source root",
                        raw.build_root
                    ),
                ));
            }
        }
        if path_overlaps(&raw.build_root, &raw.lockfile) {
            diagnostics.push(config_error(
                path,
                format!(
                    "lockfile `{}` lies inside the build root `{}`",
                    raw.lockfile, raw.build_root
                ),
            ));
        }
    }
    for (name, value) in raw.limits.rows() {
        if value == 0 {
            diagnostics.push(config_error(
                path,
                format!("limits.{name} must be a positive integer"),
            ));
        }
    }

    // Lexicon sources: disjoint schemas, unique by package, sorted (§10.1).
    let mut sources = Vec::new();
    for raw_source in &raw.lexicon_sources {
        if !is_package_id(&raw_source.package) {
            diagnostics.push(config_error(
                path,
                format!("`{}` is not a valid package ID", raw_source.package),
            ));
        }
        let extra = |field: &str| {
            format!(
                "lexicon_source `{}`: `{field}` does not apply to kind `{}`",
                raw_source.package, raw_source.kind
            )
        };
        match raw_source.kind.as_str() {
            "builtin" => {
                for (field, present) in [
                    ("path", raw_source.path.is_some()),
                    ("url", raw_source.url.is_some()),
                    ("revision", raw_source.revision.is_some()),
                    ("subdirectory", raw_source.subdirectory.is_some()),
                ] {
                    if present {
                        diagnostics.push(config_error(path, extra(field)));
                    }
                }
                sources.push(LexiconSource::Builtin {
                    package: raw_source.package.clone(),
                });
            }
            "path" => {
                let Some(source_path) = &raw_source.path else {
                    diagnostics.push(config_error(
                        path,
                        format!(
                            "lexicon_source `{}`: kind path requires `path`",
                            raw_source.package
                        ),
                    ));
                    continue;
                };
                if raw_source.url.is_some()
                    || raw_source.revision.is_some()
                    || raw_source.subdirectory.is_some()
                {
                    diagnostics.push(config_error(
                        path,
                        format!(
                            "lexicon_source `{}`: kind path accepts no URL or revision",
                            raw_source.package
                        ),
                    ));
                }
                if !is_project_relative(source_path) {
                    diagnostics.push(config_error(
                        path,
                        format!("lexicon_source path `{source_path}` is not project-relative"),
                    ));
                }
                sources.push(LexiconSource::Path {
                    package: raw_source.package.clone(),
                    path: source_path.clone(),
                });
            }
            "git" => {
                let (Some(url), Some(revision), Some(subdirectory)) = (
                    &raw_source.url,
                    &raw_source.revision,
                    &raw_source.subdirectory,
                ) else {
                    diagnostics.push(config_error(
                        path,
                        format!(
                            "lexicon_source `{}`: kind git requires url, revision, and subdirectory",
                            raw_source.package
                        ),
                    ));
                    continue;
                };
                if raw_source.path.is_some() {
                    diagnostics.push(config_error(path, extra("path")));
                }
                if !url.starts_with("https://") {
                    diagnostics.push(config_error(path, format!("git URL `{url}` is not HTTPS")));
                }
                if revision.len() != 40
                    || !revision
                        .bytes()
                        .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
                {
                    diagnostics.push(config_error(
                        path,
                        format!(
                            "git revision `{revision}` is not an exact 40-lowercase-hex commit"
                        ),
                    ));
                }
                if !is_project_relative(subdirectory) {
                    diagnostics.push(config_error(
                        path,
                        format!("git subdirectory `{subdirectory}` is not relative"),
                    ));
                }
                sources.push(LexiconSource::Git {
                    package: raw_source.package.clone(),
                    url: url.clone(),
                    revision: revision.clone(),
                    subdirectory: subdirectory.clone(),
                });
            }
            other => diagnostics.push(config_error(
                path,
                format!("`{other}` is not a lexicon source kind"),
            )),
        }
    }
    let mut seen_packages = std::collections::BTreeSet::new();
    for source in &sources {
        if !seen_packages.insert(source.package().to_owned()) {
            diagnostics.push(config_error(
                path,
                format!("lexicon_source `{}` is configured twice", source.package()),
            ));
        }
    }
    if !sources
        .windows(2)
        .all(|pair| pair[0].package() < pair[1].package())
    {
        diagnostics.push(config_error(
            path,
            "lexicon_source tables must be sorted by package",
        ));
    }

    // The optional PDF provider (§10.3, §19.7).
    let pdf = match &raw.pdf {
        None => None,
        Some(raw_pdf) => {
            if raw_pdf.mode != "external" {
                diagnostics.push(config_error(
                    path,
                    "only pdf mode `external` exists in language 1.0",
                ));
            }
            if !is_project_relative(&raw_pdf.program) {
                diagnostics.push(config_error(
                    path,
                    format!("pdf program `{}` is not project-relative", raw_pdf.program),
                ));
            }
            let placeholders = ["{input}", "{out_dir}", "{stem}"];
            for argv_name in ["version_argv", "compile_argv"] {
                let argv = if argv_name == "version_argv" {
                    &raw_pdf.version_argv
                } else {
                    &raw_pdf.compile_argv
                };
                if argv.is_empty() {
                    diagnostics.push(config_error(path, format!("pdf {argv_name} is empty")));
                }
                for argument in argv {
                    let embedded = placeholders
                        .iter()
                        .any(|p| argument.contains(p) && argument != *p);
                    if embedded {
                        diagnostics.push(config_error(
                            path,
                            format!(
                                "pdf {argv_name}: a placeholder embedded in a larger argument is forbidden: `{argument}`"
                            ),
                        ));
                    }
                }
            }
            for placeholder in ["{input}", "{out_dir}"] {
                let count = raw_pdf
                    .compile_argv
                    .iter()
                    .filter(|argument| argument.as_str() == placeholder)
                    .count();
                if count != 1 {
                    diagnostics.push(config_error(
                        path,
                        format!("pdf compile_argv must use `{placeholder}` exactly once"),
                    ));
                }
            }
            if raw_pdf
                .version_argv
                .iter()
                .any(|argument| placeholders.iter().any(|p| argument.contains(p)))
            {
                diagnostics.push(config_error(
                    path,
                    "pdf version_argv accepts no placeholders",
                ));
            }
            if raw_pdf.output.matches("{stem}").count() != 1
                || raw_pdf.output.contains("{input}")
                || raw_pdf.output.contains("{out_dir}")
            {
                diagnostics.push(config_error(
                    path,
                    "pdf output must use `{stem}` exactly once and no other placeholder",
                ));
            }
            // §19.7: the provider may only ever satisfy the protocol inside
            // `{out_dir}`, so the output names one file there. A pattern
            // carrying a separator or a `..` segment is refused at load,
            // not at the provider run: a configuration that can never
            // succeed is a configuration error (LLC0101).
            if !crate::backend::pdf::is_bare_file_name(&raw_pdf.output) {
                diagnostics.push(config_error(
                    path,
                    format!(
                        "pdf output `{}` is not a bare file name: it must contain no `/`, `\\`, or `..` segment",
                        raw_pdf.output
                    ),
                ));
            }
            for resource in &raw_pdf.resources {
                if !is_project_relative(resource) {
                    diagnostics.push(config_error(
                        path,
                        format!("pdf resource `{resource}` is not project-relative"),
                    ));
                }
            }
            Some(PdfProvider {
                program: raw_pdf.program.clone(),
                program_sha256: parse_hex64(
                    path,
                    "pdf.program_sha256",
                    &raw_pdf.program_sha256,
                    &mut diagnostics,
                ),
                version_argv: raw_pdf.version_argv.clone(),
                version_stdout_sha256: parse_hex64(
                    path,
                    "pdf.version_stdout_sha256",
                    &raw_pdf.version_stdout_sha256,
                    &mut diagnostics,
                ),
                compile_argv: raw_pdf.compile_argv.clone(),
                output: raw_pdf.output.clone(),
                resources: raw_pdf.resources.clone(),
            })
        }
    };

    if diagnostics.is_empty() {
        Ok(ProjectConfig {
            name: raw.name,
            module_prefix: raw.module_prefix,
            source_roots: raw.source_roots,
            entrypoints: raw.entrypoints,
            build_root: raw.build_root,
            lockfile: raw.lockfile,
            lean_workspace: raw.lean_workspace,
            lexicon_sources: sources,
            limits: raw.limits,
            pdf,
        })
    } else {
        Err(diagnostics)
    }
}

/// A TOML basic string: quotes and backslashes escaped, every control
/// scalar (U+0000..U+001F and U+007F) written as a four-hex-digit `\u` escape.
#[must_use]
pub fn toml_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for scalar in value.chars() {
        match scalar {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 || c as u32 == 0x7F => {
                out.push_str(&format!("\\u{:04X}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn toml_array(values: &[String]) -> String {
    let items: Vec<String> = values.iter().map(|value| toml_string(value)).collect();
    format!("[{}]", items.join(", "))
}

impl ProjectConfig {
    /// The canonical TOML serialization (§10.1): fixed key order, sorted
    /// tables, LF, one final LF, no comments.
    #[must_use]
    pub fn canonical_toml(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("spec = {}\n", toml_string("lexlean/project/1")));
        out.push_str(&format!("name = {}\n", toml_string(&self.name)));
        out.push_str(&format!(
            "language = {}\n",
            toml_string(crate::LANGUAGE_VERSION)
        ));
        out.push_str(&format!(
            "module_prefix = {}\n",
            toml_string(&self.module_prefix)
        ));
        out.push_str(&format!(
            "source_roots = {}\n",
            toml_array(&self.source_roots)
        ));
        out.push_str(&format!(
            "entrypoints = {}\n",
            toml_array(&self.entrypoints)
        ));
        out.push_str(&format!("build_root = {}\n", toml_string(&self.build_root)));
        out.push_str(&format!("lockfile = {}\n", toml_string(&self.lockfile)));
        out.push_str(&format!(
            "lean_workspace = {}\n",
            toml_string(&self.lean_workspace)
        ));
        out.push_str(&format!(
            "lean_toolchain = {}\n",
            toml_string(crate::LEAN_TOOLCHAIN)
        ));
        let mut sources = self.lexicon_sources.clone();
        sources.sort_by(|a, b| a.package().cmp(b.package()));
        // §10.1 requires the field, so the empty case is written as the empty
        // array rather than omitted. Writing nothing would emit canonical text
        // that does not parse back --- the field would be missing, which
        // `CF-01` requires be rejected rather than defaulted --- and
        // `lock --check`, which compares a configuration against its own
        // canonical serialization, would fail on its own output. A project
        // with no declared source is reachable now that a package can be
        // unconditional: `examples/uor-atlas` declares none and still resolves
        // the Atlas closure.
        if sources.is_empty() {
            out.push_str("lexicon_source = []\n");
        }
        for source in &sources {
            out.push_str("\n[[lexicon_source]]\n");
            match source {
                LexiconSource::Builtin { package } => {
                    out.push_str(&format!("package = {}\n", toml_string(package)));
                    out.push_str("kind = \"builtin\"\n");
                }
                LexiconSource::Path { package, path } => {
                    out.push_str(&format!("package = {}\n", toml_string(package)));
                    out.push_str("kind = \"path\"\n");
                    out.push_str(&format!("path = {}\n", toml_string(path)));
                }
                LexiconSource::Git {
                    package,
                    url,
                    revision,
                    subdirectory,
                } => {
                    out.push_str(&format!("package = {}\n", toml_string(package)));
                    out.push_str("kind = \"git\"\n");
                    out.push_str(&format!("url = {}\n", toml_string(url)));
                    out.push_str(&format!("revision = {}\n", toml_string(revision)));
                    out.push_str(&format!("subdirectory = {}\n", toml_string(subdirectory)));
                }
            }
        }
        out.push_str("\n[limits]\n");
        for (name, value) in self.limits.rows() {
            out.push_str(&format!("{name} = {value}\n"));
        }
        if let Some(pdf) = &self.pdf {
            out.push_str("\n[pdf]\n");
            out.push_str("mode = \"external\"\n");
            out.push_str(&format!("program = {}\n", toml_string(&pdf.program)));
            out.push_str(&format!(
                "program_sha256 = {}\n",
                toml_string(&pdf.program_sha256.to_hex())
            ));
            out.push_str(&format!(
                "version_argv = {}\n",
                toml_array(&pdf.version_argv)
            ));
            out.push_str(&format!(
                "version_stdout_sha256 = {}\n",
                toml_string(&pdf.version_stdout_sha256.to_hex())
            ));
            out.push_str(&format!(
                "compile_argv = {}\n",
                toml_array(&pdf.compile_argv)
            ));
            out.push_str(&format!("output = {}\n", toml_string(&pdf.output)));
            out.push_str(&format!("resources = {}\n", toml_array(&pdf.resources)));
        }
        out
    }

    /// SHA-256 of the canonical serialization, `project_config_sha256`.
    #[must_use]
    pub fn config_sha256(&self) -> Sha256Digest {
        Sha256Digest::of(self.canonical_toml().as_bytes())
    }
}
