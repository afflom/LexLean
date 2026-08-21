//! Derive the `lexlean.uor.atlas` entry set from the vendored library.
//!
//! The pack has one entry per live Atlas source-register row, and
//! `audit-atlas-denotations` fails the moment the two disagree in either
//! direction. That audit is what makes this generator necessary rather than
//! convenient: entries are committed data, and a committed set with no way to
//! regenerate it is a table someone has to maintain by hand against a library
//! that keeps growing. Running this after new labels land is the whole
//! maintenance procedure.
//!
//! Two properties of the surfaces are load-bearing rather than cosmetic.
//! Numerals are not renderer-safe in the text channel, so a label's number is
//! spelled. And every surface ends in a closing word, which makes the set
//! prefix-free: without it `T59p`'s surface followed by `lexlean.std.nat`'s
//! `zero` reads as `T59p0`, and a document citing both has two distinct linked
//! interpretations. `audit-atlas-exercise` holds both properties.

use std::collections::BTreeMap;
use std::path::Path;

use crate::Fail;

/// The word for each label prefix. The ambient lemmas of section 19.6 are
/// named for what they are rather than for their initials, because a reader
/// spelling `RH1` aloud says "ring homomorphism one", not "R H one".
const PREFIX_WORDS: [(&str, &str); 20] = [
    ("A", "base"),
    ("BC", "base change"),
    ("D", "definition"),
    ("DV", "divisibility"),
    ("F", "fact"),
    ("FI", "field injection"),
    ("FR", "free rank"),
    ("IG", "integral group"),
    ("LI", "linear independence"),
    ("M", "morphism identity"),
    ("P", "premise"),
    ("QL", "quotient"),
    ("RC", "ring condition"),
    ("RH", "ring homomorphism"),
    ("RP", "representation"),
    ("S", "scale"),
    ("SD", "self duality"),
    ("T", "theorem"),
    ("TI", "tensor identity"),
    ("V", "verification"),
];

const ONES: [&str; 20] = [
    "zero",
    "one",
    "two",
    "three",
    "four",
    "five",
    "six",
    "seven",
    "eight",
    "nine",
    "ten",
    "eleven",
    "twelve",
    "thirteen",
    "fourteen",
    "fifteen",
    "sixteen",
    "seventeen",
    "eighteen",
    "nineteen",
];

const TENS: [&str; 10] = [
    "", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety",
];

fn spell(value: u32) -> String {
    if value < 20 {
        return ONES[value as usize].to_owned();
    }
    if value < 100 {
        let (tens, rest) = (value / 10, value % 10);
        return if rest == 0 {
            TENS[tens as usize].to_owned()
        } else {
            format!("{} {}", TENS[tens as usize], ONES[rest as usize])
        };
    }
    let (hundreds, rest) = (value / 100, value % 100);
    if rest == 0 {
        format!("{} hundred", ONES[hundreds as usize])
    } else {
        format!("{} hundred {}", ONES[hundreds as usize], spell(rest))
    }
}

/// A label's canonical text surface: `T57a` is "Atlas theorem fifty seven a
/// label".
fn surface(label: &str) -> Result<String, Fail> {
    let split = label
        .find(|c: char| !c.is_ascii_alphabetic())
        .ok_or_else(|| Fail::from(format!("`{label}` has no number")))?;
    let (prefix, rest) = label.split_at(split);
    let digits_end = rest
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(rest.len());
    let (digits, suffix) = rest.split_at(digits_end);
    let word = PREFIX_WORDS
        .iter()
        .find(|(key, _)| *key == prefix)
        .map(|(_, word)| *word)
        .ok_or_else(|| Fail::from(format!("`{label}`: no word for the prefix `{prefix}`")))?;
    let number: u32 = digits
        .parse()
        .map_err(|_| Fail::from(format!("`{label}`: `{digits}` is not a number")))?;
    let mut out = format!("Atlas {word} {}", spell(number));
    for character in suffix.chars() {
        out.push(' ');
        if let Some(digit) = character.to_digit(10) {
            out.push_str(&spell(digit));
        } else {
            out.push(character);
        }
    }
    // The closing word is what makes the surface set prefix-free.
    out.push_str(" label");
    Ok(out)
}

/// Every label the vendored library declares, with the module that declares it
/// and its fully qualified name.
fn declared(root: &Path) -> Result<BTreeMap<String, (String, String)>, Fail> {
    let library = root.join("lean/uor-atlas/UorAtlas");
    let mut out = BTreeMap::new();
    let mut modules: Vec<std::path::PathBuf> = Vec::new();
    for entry in walkdir::WalkDir::new(&library)
        .follow_links(false)
        .into_iter()
        .flatten()
    {
        if entry.file_type().is_file() && entry.path().extension().is_some_and(|e| e == "lean") {
            modules.push(entry.path().to_path_buf());
        }
    }
    modules.sort();
    for path in &modules {
        let text = std::fs::read_to_string(path)?;
        let module = format!(
            "UorAtlas.{}",
            path.strip_prefix(&library)
                .unwrap_or(path)
                .with_extension("")
                .to_string_lossy()
                .replace(['/', '\\'], ".")
        );
        let namespace = text
            .lines()
            .find_map(|line| line.strip_prefix("namespace "))
            .unwrap_or("UorAtlas")
            .trim()
            .to_owned();
        for name in crate::audit::declaration_names(&text) {
            out.entry(name.clone())
                .or_insert_with(|| (module.clone(), format!("{namespace}.{name}")));
        }
    }
    Ok(out)
}

/// Rewrite `language/uor/atlas/entries` from the register and the library.
pub fn generate(root: &Path, write: bool) -> Result<(), Fail> {
    let registers = root.join("language/uor/atlas-registers.toml");
    let data: toml::Value = std::fs::read_to_string(&registers)?.parse()?;
    let mut live: Vec<String> = Vec::new();
    for key in ["entry", "ambient"] {
        if let Some(items) = data.get(key).and_then(toml::Value::as_array) {
            live.extend(items.iter().filter_map(|i| i.as_str()).map(str::to_owned));
        }
    }
    live.sort();
    let declared = declared(root)?;

    let mut wanted: BTreeMap<String, String> = BTreeMap::new();
    let mut surfaces: BTreeMap<String, String> = BTreeMap::new();
    for label in &live {
        let (module, name) = declared.get(label).ok_or_else(|| {
            Fail::from(format!(
                "the Atlas source register marks `{label}` live, but the vendored library has no declaration for it"
            ))
        })?;
        let text = surface(label)?;
        if let Some(other) = surfaces.insert(text.clone(), label.clone()) {
            return Err(Fail::from(format!(
                "`{label}` and `{other}` would share the surface `{text}`"
            )));
        }
        wanted.insert(
            format!("atlas-{}", label.to_ascii_lowercase()),
            format!(
                "spec = \"lexlean/entry/1\"\nid = \"atlas-{}\"\ncategory = \"label-word\"\nsurface_arity = 0\nframe = \"atom\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"{module}\"\nname = \"{name}\"\n\n[[form]]\nid = \"atlas-{}\"\nchannel = \"text\"\nsurface = \"{text}\"\ncanonical_source = true\nfeatures = [\"sentence-case\", \"singular\"]\n",
                label.to_ascii_lowercase(),
                label.to_ascii_lowercase()
            ),
        );
    }

    let dir = root.join("language/uor/atlas/entries");
    // Entries whose id carries no digit name no label: they are the *object*
    // entries a live definition introduces --- `atlas-presentation` for `D17`
    // and the rest of that chain --- and they are written by hand, because
    // their signatures are what make one non-interchangeable with another and
    // no rule derives those from a Lean declaration. The generator owns the
    // label entries and leaves the object entries alone.
    let is_label_entry =
        |id: &str| id.starts_with("atlas-") && id.chars().any(|c| c.is_ascii_digit());
    let mut stale = Vec::new();
    if dir.exists() {
        for entry in std::fs::read_dir(&dir)?.flatten() {
            let path = entry.path();
            if path.extension().is_some_and(|e| e == "toml") {
                let id = path
                    .file_stem()
                    .unwrap_or_default()
                    .to_string_lossy()
                    .into_owned();
                if !is_label_entry(&id) {
                    continue;
                }
                match wanted.get(&id) {
                    Some(expected) if std::fs::read_to_string(&path)? == *expected => {}
                    _ => stale.push(id),
                }
            }
        }
    }
    let missing: Vec<&String> = wanted
        .keys()
        .filter(|id| !dir.join(format!("{id}.toml")).exists())
        .collect();

    if !write {
        if stale.is_empty() && missing.is_empty() {
            println!(
                "atlas-pack: {} entries derived from the library are current",
                wanted.len()
            );
            return Ok(());
        }
        return Err(Fail::from(format!(
            "the Atlas pack is not the one the library implies: {} stale, {} missing; run `cargo xtask atlas-pack --write`",
            stale.len(),
            missing.len()
        )));
    }

    std::fs::create_dir_all(&dir)?;
    for entry in std::fs::read_dir(&dir)?.flatten() {
        let path = entry.path();
        let id = path
            .file_stem()
            .unwrap_or_default()
            .to_string_lossy()
            .into_owned();
        if path.extension().is_some_and(|e| e == "toml") && is_label_entry(&id) {
            std::fs::remove_file(path)?;
        }
    }
    for (id, body) in &wanted {
        std::fs::write(dir.join(format!("{id}.toml")), body)?;
    }

    // The exhaustive module is derived from the same set. `audit-atlas-exercise`
    // requires every entry to be cited by a committed document, so a pack that
    // grew without it would fail the gate; writing both here keeps the two in
    // step by construction rather than by remembering.
    let module = root.join("examples/uor-atlas/src/Labels.lex.tex");
    if module.exists() {
        let mut out =
            String::from("\\begin{lexlean}{Labels}\n\\title{Atlas definition one label}\n");
        for id in wanted.keys() {
            let text = surfaces
                .iter()
                .find(|(_, label)| format!("atlas-{}", label.to_ascii_lowercase()) == **id)
                .map(|(text, _)| text.clone())
                .unwrap_or_default();
            out.push_str(&format!(
                "\n\\begin{{section}}{{{id}}}\n\\heading{{{text}}}\n\\end{{section}}\n"
            ));
        }
        // No blank line before the closing environment: that is what `fmt`
        // canonicalises to, and a generator that needed a formatting pass after
        // it would fail `fmt --check` on its own output every time.
        out.push_str("\\end{lexlean}\n");
        std::fs::write(&module, out)?;
        println!(
            "atlas-pack: wrote the exhaustive module citing {} entries",
            wanted.len()
        );
    }

    println!("atlas-pack: wrote {} entries", wanted.len());
    Ok(())
}
