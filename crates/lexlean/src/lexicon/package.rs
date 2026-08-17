//! Lexicon package loading and validation (SPEC.md §13.1, §13.11).

use std::collections::BTreeMap;

use serde::Deserialize;

use crate::artifact::content_id::{tree_digest, Sha256Digest};
use crate::code;
use crate::diagnostic::{Diagnostic, Span};
use crate::lexicon::entry::{parse_entry, Denotation, Entry, EntryContext};
use crate::lexicon::lse::{self, is_entry_id, is_package_id, ConstInfo, QualifiedId};

/// A package import reference, `package@version`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PackageRef {
    /// The package ID.
    pub package: String,
    /// The exact version.
    pub version: String,
}

impl PackageRef {
    /// Parse and validate `package@version`.
    pub fn parse(text: &str) -> Result<Self, String> {
        let (package, version) = text
            .split_once('@')
            .ok_or_else(|| format!("`{text}` is not a `package@version` reference"))?;
        if !is_package_id(package) {
            return Err(format!("`{package}` is not a valid package ID"));
        }
        semver::Version::parse(version)
            .map_err(|error| format!("`{version}` is not an exact version: {error}"))?;
        Ok(Self {
            package: package.to_owned(),
            version: version.to_owned(),
        })
    }
}

impl std::fmt::Display for PackageRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{}", self.package, self.version)
    }
}

/// One loaded and validated lexicon package.
#[derive(Debug, Clone)]
pub struct LexiconPackage {
    /// The package ID.
    pub id: String,
    /// The exact version.
    pub version: String,
    /// Exact, sorted, unique imports.
    pub imports: Vec<PackageRef>,
    /// Entries by local ID.
    pub entries: BTreeMap<String, Entry>,
    /// SHA-256 of the manifest bytes.
    pub manifest_sha256: Sha256Digest,
    /// The §11.5 tree digest over `lexicon.toml` and `entries/`.
    pub tree_sha256: Sha256Digest,
    /// The participating files and their byte totals, for the explicit
    /// resource policy (§10.2).
    pub total_bytes: usize,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawManifest {
    spec: String,
    package: String,
    version: String,
    language: String,
    imports: Vec<String>,
}

/// Scan TOML text for a comment outside every string form. Comments are
/// forbidden in project, lock, and lexicon files (§10.1, §11.1, §13.1).
#[must_use]
pub fn toml_comment_at(text: &str) -> Option<usize> {
    #[derive(PartialEq)]
    enum State {
        Plain,
        Basic,
        Literal,
        MultiBasic,
        MultiLiteral,
    }
    let bytes = text.as_bytes();
    let mut state = State::Plain;
    let mut index = 0;
    while index < bytes.len() {
        let rest = &bytes[index..];
        match state {
            State::Plain => {
                if rest.starts_with(b"\"\"\"") {
                    state = State::MultiBasic;
                    index += 3;
                } else if rest.starts_with(b"'''") {
                    state = State::MultiLiteral;
                    index += 3;
                } else {
                    match bytes[index] {
                        b'"' => state = State::Basic,
                        b'\'' => state = State::Literal,
                        b'#' => return Some(index),
                        _ => {}
                    }
                    index += 1;
                }
            }
            State::Basic => {
                match bytes[index] {
                    b'\\' => index += 1,
                    b'"' | b'\n' => state = State::Plain,
                    _ => {}
                }
                index += 1;
            }
            State::Literal => {
                if matches!(bytes[index], b'\'' | b'\n') {
                    state = State::Plain;
                }
                index += 1;
            }
            State::MultiBasic => {
                if rest.starts_with(b"\"\"\"") {
                    state = State::Plain;
                    index += 3;
                } else {
                    if bytes[index] == b'\\' {
                        index += 1;
                    }
                    index += 1;
                }
            }
            State::MultiLiteral => {
                if rest.starts_with(b"'''") {
                    state = State::Plain;
                    index += 3;
                } else {
                    index += 1;
                }
            }
        }
    }
    None
}

fn file_error(path: &str, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code!("LLR3004"), message).with_span(Span::whole_file(path))
}

/// The entry file path for a local entry ID: `entries/` plus each
/// dot-separated segment as a directory and `.toml` on the final segment
/// (§13.1).
#[must_use]
pub fn entry_path(local_id: &str) -> String {
    format!("entries/{}.toml", local_id.replace('.', "/"))
}

/// What package loading needs from the language bootstrap and the project's
/// explicit resource policy.
#[derive(Debug, Clone, Copy)]
pub struct LoadContext<'a> {
    /// The §12.4 always-forbidden controls (`language/bootstrap.toml`).
    pub forbidden_controls: &'a [String],
    /// The configured `max_scope_depth`, bounding LSE/LRE nesting (§25.5).
    pub max_scope_depth: u64,
}

/// Load one package from its participating files, given as
/// `(package-relative path, bytes)`: exactly `lexicon.toml` and the files
/// under `entries/`. Paths must already be sorted bytewise.
#[allow(clippy::too_many_lines)]
pub fn load_package(
    display_root: &str,
    files: &[(String, Vec<u8>)],
    expected: Option<&PackageRef>,
    ctx: &LoadContext<'_>,
) -> Result<LexiconPackage, Vec<Diagnostic>> {
    let mut diagnostics: Vec<Diagnostic> = Vec::new();
    let display = |relative: &str| format!("{display_root}/{relative}");

    let borrowed: Vec<(&str, &[u8])> = files
        .iter()
        .map(|(path, bytes)| (path.as_str(), bytes.as_slice()))
        .collect();
    let tree_sha256 = tree_digest(&borrowed);
    let total_bytes = files.iter().map(|(_, bytes)| bytes.len()).sum();

    let Some(manifest_bytes) = files
        .iter()
        .find(|(path, _)| path == "lexicon.toml")
        .map(|(_, bytes)| bytes)
    else {
        return Err(vec![Diagnostic::new(
            code!("LLR3001"),
            format!("{display_root}: lexicon.toml is missing"),
        )]);
    };
    let manifest_sha256 = Sha256Digest::of(manifest_bytes);
    let manifest_path = display("lexicon.toml");
    let Ok(manifest_text) = std::str::from_utf8(manifest_bytes) else {
        return Err(vec![file_error(
            &manifest_path,
            "lexicon.toml is not UTF-8",
        )]);
    };
    if toml_comment_at(manifest_text).is_some() {
        diagnostics.push(file_error(&manifest_path, "comments are forbidden"));
    }
    let manifest: RawManifest = match toml::from_str(manifest_text) {
        Ok(manifest) => manifest,
        Err(parse_error) => {
            diagnostics.push(file_error(
                &manifest_path,
                format!("invalid lexicon manifest: {parse_error}"),
            ));
            return Err(diagnostics);
        }
    };
    if manifest.spec != "lexlean/lexicon/1" {
        diagnostics.push(
            Diagnostic::new(
                code!("LLC0103"),
                format!("unsupported lexicon schema `{}`", manifest.spec),
            )
            .with_span(Span::whole_file(&manifest_path)),
        );
    }
    if manifest.language != crate::LANGUAGE_VERSION {
        diagnostics.push(
            Diagnostic::new(
                code!("LLC0103"),
                format!("unsupported lexicon language `{}`", manifest.language),
            )
            .with_span(Span::whole_file(&manifest_path)),
        );
    }
    if !is_package_id(&manifest.package) {
        diagnostics.push(file_error(
            &manifest_path,
            format!("`{}` is not a valid package ID", manifest.package),
        ));
    }
    if semver::Version::parse(&manifest.version).is_err() {
        diagnostics.push(file_error(
            &manifest_path,
            format!("`{}` is not an exact version", manifest.version),
        ));
    }
    if let Some(expected_ref) = expected {
        if expected_ref.package != manifest.package || expected_ref.version != manifest.version {
            diagnostics.push(Diagnostic::new(
                code!("LLR3001"),
                format!(
                    "{display_root}: expected {expected_ref}, found {}@{}",
                    manifest.package, manifest.version
                ),
            ));
        }
    }
    let mut imports = Vec::new();
    for import_text in &manifest.imports {
        match PackageRef::parse(import_text) {
            Ok(reference) => imports.push(reference),
            Err(parse_error) => diagnostics.push(file_error(&manifest_path, parse_error)),
        }
    }
    // "Exact, sorted, and unique" (§13.1) is a property of the manifest
    // text: the `package@version` strings sort bytewise and no two are
    // equal, and no package is imported twice at different versions.
    if !manifest
        .imports
        .windows(2)
        .all(|pair| pair[0].as_bytes() < pair[1].as_bytes())
    {
        diagnostics.push(file_error(
            &manifest_path,
            format!(
                "imports must be exact, sorted bytewise, and unique; found [{}]",
                manifest.imports.join(", ")
            ),
        ));
    }
    let import_packages: std::collections::BTreeSet<&str> =
        imports.iter().map(|r| r.package.as_str()).collect();
    if import_packages.len() != imports.len() {
        diagnostics.push(file_error(
            &manifest_path,
            "a package is imported at most once",
        ));
    }
    if imports
        .iter()
        .any(|reference| reference.package == manifest.package)
    {
        diagnostics.push(Diagnostic::new(
            code!("LLR3003"),
            format!("{}: a package cannot import itself", manifest.package),
        ));
    }

    let is_core = manifest.package == "lexlean.core";
    let entry_ctx = EntryContext {
        is_core,
        forbidden_controls: ctx.forbidden_controls,
        max_scope_depth: ctx.max_scope_depth,
    };
    let mut entries: BTreeMap<String, Entry> = BTreeMap::new();
    for (relative, bytes) in files {
        if relative == "lexicon.toml" {
            continue;
        }
        let shown = display(relative);
        let Some(inner) = relative
            .strip_prefix("entries/")
            .and_then(|rest| rest.strip_suffix(".toml"))
        else {
            diagnostics.push(file_error(
                &shown,
                "a package contains lexicon.toml and entries/ only",
            ));
            continue;
        };
        let local_id = inner.replace('/', ".");
        if !is_entry_id(&local_id) || entry_path(&local_id) != *relative {
            diagnostics.push(file_error(&shown, "invalid entry path"));
            continue;
        }
        let Ok(entry_text) = std::str::from_utf8(bytes) else {
            diagnostics.push(file_error(&shown, "entry file is not UTF-8"));
            continue;
        };
        if toml_comment_at(entry_text).is_some() {
            diagnostics.push(file_error(&shown, "comments are forbidden"));
            continue;
        }
        match parse_entry(&shown, entry_text, &entry_ctx) {
            Ok(entry) => {
                if entry.id != local_id {
                    diagnostics.push(file_error(
                        &shown,
                        format!("entry ID `{}` does not match its path", entry.id),
                    ));
                    continue;
                }
                if entries.insert(entry.id.clone(), entry).is_some() {
                    diagnostics.push(
                        Diagnostic::new(
                            code!("LLR3002"),
                            format!("duplicate entry `{local_id}` in {}", manifest.package),
                        )
                        .with_span(Span::whole_file(&shown)),
                    );
                }
            }
            Err(mut entry_diagnostics) => diagnostics.append(&mut entry_diagnostics),
        }
    }

    // Package-local signature check (§13.7, §13.11 "invalid LSE"): a
    // signature or defined value that is ill-typed on its own — a term where
    // a type is required, an application over the explicit arity of an
    // entry of this package, a defined value disagreeing with its
    // signature — is rejected when the package loads (`lock`), not first
    // when a build links the closure. Constants of other packages are
    // opaque here; the closure repeats the check with every reference
    // resolved.
    if diagnostics.is_empty() {
        let lookup = |id: &QualifiedId| -> ConstInfo<'_> {
            if id.package != manifest.package {
                return ConstInfo::Opaque;
            }
            match entries.get(&id.entry) {
                Some(entry) => match &entry.signature {
                    Some(signature) => ConstInfo::Signature {
                        signature,
                        defined: matches!(entry.denotation, Denotation::Defined { .. }),
                    },
                    None => ConstInfo::NoSignature,
                },
                // An unresolved same-package reference is the closure's
                // `LLR3005`; it is not judged here.
                None => ConstInfo::Opaque,
            }
        };
        for entry in entries.values() {
            let shown = display(&entry_path(&entry.id));
            if let Some(signature) = &entry.signature {
                if let Err(type_error) = lse::check_signature(signature, &lookup) {
                    diagnostics.push(file_error(
                        &shown,
                        format!(
                            "signature `{}` is not well-typed: {type_error}",
                            signature.print(false)
                        ),
                    ));
                }
            }
            if let Denotation::Defined { value, .. } = &entry.denotation {
                if let Err(type_error) = lse::check_value(value, entry.signature.as_ref(), &lookup)
                {
                    diagnostics.push(file_error(
                        &shown,
                        format!("defined value is not well-typed: {type_error}"),
                    ));
                }
            }
        }
    }

    if diagnostics.is_empty() {
        Ok(LexiconPackage {
            id: manifest.package,
            version: manifest.version,
            imports,
            entries,
            manifest_sha256,
            tree_sha256,
            total_bytes,
        })
    } else {
        Err(diagnostics)
    }
}
