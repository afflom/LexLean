//! Embeds the normative language data into the compiler binary (SPEC.md §12.3,
//! §21.2): every regular file under `language/` and `schemas/`, and the
//! committed axiom-parser and canonical-JSON golden fixtures. The runtime
//! computes the compiler-semantics ID from exactly this set, and repository
//! tests recompute it from disk and compare (RP-10).

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// The repository-root-relative directories whose regular files participate
/// in the compiler-semantics digest (SPEC.md §21.2).
const SEMANTIC_DIRS: [&str; 4] = [
    "language",
    "schemas",
    "tests/golden/axiom-parser",
    "tests/golden/canonical-json",
];

fn main() {
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("cargo sets this"));
    let repo_root = manifest
        .ancestors()
        .nth(2)
        .expect("crates/lexlean is two levels below the repository root")
        .to_path_buf();

    let mut files: Vec<(String, PathBuf)> = Vec::new();
    for dir in SEMANTIC_DIRS {
        let root = repo_root.join(dir);
        println!("cargo:rerun-if-changed={}", root.display());
        collect(&root, dir, &mut files);
    }
    // Bytewise-sorted repository-relative path order, the §11.5 tree order.
    files.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));

    let mut out = String::new();
    out.push_str(
        "/// Every embedded normative file as `(repository-relative path, bytes)`,\n\
         /// in bytewise-sorted path order.\n\
         pub static FILES: &[(&str, &[u8])] = &[\n",
    );
    for (rel, abs) in &files {
        println!("cargo:rerun-if-changed={}", abs.display());
        out.push_str(&format!(
            "    ({:?}, include_bytes!({:?})),\n",
            rel,
            abs.display().to_string()
        ));
    }
    out.push_str("];\n");

    let dest = PathBuf::from(env::var("OUT_DIR").expect("cargo sets this")).join("embedded.rs");
    fs::write(&dest, out).expect("write embedded.rs");
}

fn collect(dir: &Path, rel: &str, out: &mut Vec<(String, PathBuf)>) {
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    let mut children: Vec<_> = entries.filter_map(Result::ok).collect();
    children.sort_by_key(std::fs::DirEntry::file_name);
    for child in children {
        let path = child.path();
        let name = child.file_name();
        let name = name.to_str().expect("normative paths are UTF-8");
        let child_rel = format!("{rel}/{name}");
        let file_type = child.file_type().expect("file type is readable");
        if file_type.is_dir() {
            collect(&path, &child_rel, out);
        } else if file_type.is_file() {
            out.push((child_rel, path));
        } else {
            panic!("{child_rel}: normative data must contain only regular files");
        }
    }
}
