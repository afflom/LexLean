//! Content identity (SPEC.md §21.1–§21.5, §22.9, §19.8): the frame function,
//! the tree digest, and every labeled hash recipe.

use sha2::{Digest, Sha256};

/// A SHA-256 digest with lowercase-hex display.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Sha256Digest(pub [u8; 32]);

impl Sha256Digest {
    /// Hash raw bytes.
    #[must_use]
    pub fn of(bytes: &[u8]) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(bytes);
        Self(hasher.finalize().into())
    }

    /// The 64-character lowercase hexadecimal form.
    #[must_use]
    pub fn to_hex(&self) -> String {
        let mut out = String::with_capacity(64);
        for byte in self.0 {
            out.push(char::from_digit(u32::from(byte >> 4), 16).expect("nibble"));
            out.push(char::from_digit(u32::from(byte & 0xf), 16).expect("nibble"));
        }
        out
    }

    /// Parse 64 lowercase hex digits.
    pub fn from_hex(text: &str) -> Result<Self, String> {
        let bytes = text.as_bytes();
        if bytes.len() != 64 {
            return Err(format!("expected 64 hex digits, found {}", bytes.len()));
        }
        let mut out = [0u8; 32];
        for (index, chunk) in bytes.chunks_exact(2).enumerate() {
            let value = |b: u8| -> Result<u8, String> {
                match b {
                    b'0'..=b'9' => Ok(b - b'0'),
                    b'a'..=b'f' => Ok(b - b'a' + 10),
                    _ => Err("lowercase hexadecimal is mandatory".to_owned()),
                }
            };
            out[index] = (value(chunk[0])? << 4) | value(chunk[1])?;
        }
        Ok(Self(out))
    }
}

impl std::fmt::Display for Sha256Digest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_hex())
    }
}

/// An incremental framed hasher over one labeled recipe (§21.1).
pub struct FramedHasher {
    hasher: Sha256,
}

impl FramedHasher {
    /// Start a recipe with its domain-separation prefix, e.g.
    /// `"lexlean-source-v1\0"`.
    #[must_use]
    pub fn new(domain: &str) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(domain.as_bytes());
        hasher.update([0u8]);
        Self { hasher }
    }

    /// Append one `frame(label, bytes)` (§21.1).
    pub fn frame(&mut self, label: &str, bytes: &[u8]) {
        let label_bytes = label.as_bytes();
        self.hasher.update(
            u32::try_from(label_bytes.len())
                .expect("label fits u32")
                .to_be_bytes(),
        );
        self.hasher.update(label_bytes);
        self.hasher.update((bytes.len() as u64).to_be_bytes());
        self.hasher.update(bytes);
    }

    /// Finish the recipe.
    #[must_use]
    pub fn finish(self) -> Sha256Digest {
        Sha256Digest(self.hasher.finalize().into())
    }
}

/// The §11.5 tree digest over `(relative path, bytes)` rows. The caller
/// supplies rows already restricted to participating files; this function
/// enforces bytewise-sorted path order and unique paths.
#[must_use]
pub fn tree_digest(files: &[(&str, &[u8])]) -> Sha256Digest {
    debug_assert!(
        files
            .windows(2)
            .all(|pair| pair[0].0.as_bytes() < pair[1].0.as_bytes()),
        "tree digest input must be strictly sorted by path bytes"
    );
    let mut hasher = Sha256::new();
    hasher.update(b"lexlean-tree-v1");
    hasher.update([0u8]);
    for (path, bytes) in files {
        let path_bytes = path.as_bytes();
        hasher.update(
            u32::try_from(path_bytes.len())
                .expect("path fits u32")
                .to_be_bytes(),
        );
        hasher.update(path_bytes);
        hasher.update((bytes.len() as u64).to_be_bytes());
        hasher.update(bytes);
    }
    Sha256Digest(hasher.finalize().into())
}

/// The source ID (§21.3). `sources` are `(project-relative path, normalized
/// bytes)` in sorted path order.
#[must_use]
pub fn source_id(
    canonical_project_toml: &[u8],
    canonical_lock: &[u8],
    sources: &[(String, Vec<u8>)],
) -> Sha256Digest {
    let mut hasher = FramedHasher::new("lexlean-source-v1");
    hasher.frame("project", canonical_project_toml);
    hasher.frame("lock", canonical_lock);
    for (path, bytes) in sources {
        hasher.frame("path", path.as_bytes());
        hasher.frame("source", bytes);
    }
    hasher.finish()
}

/// The semantic ID (§21.4).
#[must_use]
pub fn semantic_id(
    compiler_semantics: Sha256Digest,
    linked_ir_json: &str,
    lexicon_closure_json: &str,
) -> Sha256Digest {
    let mut hasher = FramedHasher::new("lexlean-semantic-v1");
    hasher.frame("compiler-semantics", &compiler_semantics.0);
    hasher.frame("language", crate::LANGUAGE_VERSION.as_bytes());
    hasher.frame("toolchain", crate::LEAN_TOOLCHAIN.as_bytes());
    hasher.frame("linked-ir", linked_ir_json.as_bytes());
    hasher.frame("lexicon-closure", lexicon_closure_json.as_bytes());
    hasher.finish()
}

/// The build ID (§21.5).
#[must_use]
pub fn build_id(source: Sha256Digest, semantic: Sha256Digest) -> Sha256Digest {
    let mut hasher = FramedHasher::new("lexlean-build-v1");
    hasher.frame("source-id", &source.0);
    hasher.frame("semantic-id", &semantic.0);
    hasher.finish()
}

/// The attestation ID over the canonical body without its `attestation_id`
/// field (§22.9).
#[must_use]
pub fn attestation_id(body_without_id_json: &str) -> Sha256Digest {
    let mut hasher = FramedHasher::new("lexlean-attestation-v1");
    hasher.frame("attestation-body", body_without_id_json.as_bytes());
    hasher.finish()
}

/// The PDF recipe ID (§19.8).
#[must_use]
pub fn pdf_recipe_id(
    tex_sha256: Sha256Digest,
    program_sha256: Sha256Digest,
    version_stdout_sha256: Sha256Digest,
    compile_argv_json: &str,
    resources_json: &str,
) -> Sha256Digest {
    let mut hasher = FramedHasher::new("lexlean-pdf-recipe-v1");
    hasher.frame("tex", &tex_sha256.0);
    hasher.frame("program", &program_sha256.0);
    hasher.frame("version-output", &version_stdout_sha256.0);
    hasher.frame("argv", compile_argv_json.as_bytes());
    hasher.frame("resources", resources_json.as_bytes());
    hasher.finish()
}
