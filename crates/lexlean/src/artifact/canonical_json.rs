//! The restricted canonical JSON form (SPEC.md §21.7).
//!
//! No floating-point values, no `null`, object keys in UTF-8 byte order,
//! integers in shortest decimal form, minimal escaping, no insignificant
//! whitespace. Hash recipes consume [`Json::to_canonical_string`] (no final
//! LF); files are written with exactly one final LF.

use std::collections::BTreeMap;

/// A canonical JSON value. `null` and floats do not exist (§21.7): optional
/// fields are omitted from their object instead.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Json {
    /// A boolean.
    Bool(bool),
    /// An integer; every normative numeric value fits `i64`.
    Int(i64),
    /// A string, stored as UTF-8 and escaped minimally on output.
    Str(String),
    /// An array in specified semantic order.
    Arr(Vec<Json>),
    /// An object; `BTreeMap` keeps keys in UTF-8 byte order.
    Obj(BTreeMap<String, Json>),
}

impl Json {
    /// An integer from a size, saturating at `i64::MAX` (sizes near 2^63 are
    /// impossible under the explicit resource limits).
    #[must_use]
    pub fn from_usize(value: usize) -> Self {
        Self::Int(i64::try_from(value).unwrap_or(i64::MAX))
    }

    /// Build an object from key/value pairs.
    #[must_use]
    pub fn object(pairs: Vec<(&str, Json)>) -> Self {
        Self::Obj(pairs.into_iter().map(|(k, v)| (k.to_owned(), v)).collect())
    }

    /// The canonical serialization without a trailing LF (the hashed payload
    /// form of §21.7).
    #[must_use]
    pub fn to_canonical_string(&self) -> String {
        let mut out = String::new();
        self.write(&mut out);
        out
    }

    /// The canonical file bytes: the payload plus exactly one final LF.
    #[must_use]
    pub fn to_file_bytes(&self) -> Vec<u8> {
        let mut text = self.to_canonical_string();
        text.push('\n');
        text.into_bytes()
    }

    fn write(&self, out: &mut String) {
        match self {
            Self::Bool(true) => out.push_str("true"),
            Self::Bool(false) => out.push_str("false"),
            Self::Int(value) => out.push_str(&value.to_string()),
            Self::Str(value) => write_escaped(value, out),
            Self::Arr(items) => {
                out.push('[');
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        out.push(',');
                    }
                    item.write(out);
                }
                out.push(']');
            }
            Self::Obj(object) => {
                out.push('{');
                for (index, (key, value)) in object.iter().enumerate() {
                    if index > 0 {
                        out.push(',');
                    }
                    write_escaped(key, out);
                    out.push(':');
                    value.write(out);
                }
                out.push('}');
            }
        }
    }

    /// Parse canonical JSON back from bytes, rejecting floats, `null`, and
    /// duplicate keys. Used when validating existing content-addressed
    /// output before reuse (§21.8) and when reading recorded manifests.
    pub fn parse(bytes: &[u8]) -> Result<Self, String> {
        // `serde_json::Value` keeps the last of duplicate keys silently, so
        // duplicates are detected by a byte-level scan first (§21.7).
        check_duplicate_keys(bytes)?;
        let value: serde_json::Value =
            serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
        Self::from_serde(&value)
    }

    fn from_serde(value: &serde_json::Value) -> Result<Self, String> {
        match value {
            serde_json::Value::Null => Err("canonical JSON has no null".to_owned()),
            serde_json::Value::Bool(b) => Ok(Self::Bool(*b)),
            serde_json::Value::Number(number) => number
                .as_i64()
                .map(Self::Int)
                .ok_or_else(|| format!("canonical JSON has no non-integer number: {number}")),
            serde_json::Value::String(s) => Ok(Self::Str(s.clone())),
            serde_json::Value::Array(items) => items
                .iter()
                .map(Self::from_serde)
                .collect::<Result<Vec<_>, _>>()
                .map(Self::Arr),
            serde_json::Value::Object(map) => {
                let mut object = BTreeMap::new();
                for (key, item) in map {
                    object.insert(key.clone(), Self::from_serde(item)?);
                }
                Ok(Self::Obj(object))
            }
        }
    }
}

/// Minimal JSON escaping (§21.7): the required escapes plus `\u00XX` for the
/// remaining control scalars; everything else is raw UTF-8.
fn write_escaped(text: &str, out: &mut String) {
    out.push('"');
    for scalar in text.chars() {
        match scalar {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{0008}' => out.push_str("\\b"),
            '\u{000C}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

/// A streaming duplicate-key check over raw JSON bytes: every object level
/// keeps the set of keys seen so far (as their raw escaped spelling, which
/// canonical JSON makes unique per key). Structural errors are left to the
/// full parser; only a duplicate is reported here.
fn check_duplicate_keys(bytes: &[u8]) -> Result<(), String> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Frame {
        Object,
        Array,
    }
    let mut frames: Vec<(Frame, std::collections::BTreeSet<Vec<u8>>)> = Vec::new();
    let mut index = 0usize;
    // In an object, a string directly after `{` or `,` is a key.
    let mut expecting_key = false;
    while index < bytes.len() {
        let byte = bytes[index];
        match byte {
            b'"' => {
                let start = index + 1;
                let mut end = start;
                while end < bytes.len() && bytes[end] != b'"' {
                    if bytes[end] == b'\\' {
                        end += 1;
                    }
                    end += 1;
                }
                if end >= bytes.len() {
                    return Err("unterminated string".to_owned());
                }
                if expecting_key {
                    if let Some((Frame::Object, keys)) = frames.last_mut() {
                        let key = bytes[start..end].to_vec();
                        if !keys.insert(key) {
                            return Err(format!(
                                "duplicate key {}",
                                String::from_utf8_lossy(&bytes[start..end])
                            ));
                        }
                    }
                    expecting_key = false;
                }
                index = end + 1;
                continue;
            }
            b'{' => {
                frames.push((Frame::Object, std::collections::BTreeSet::new()));
                expecting_key = true;
            }
            b'[' => {
                frames.push((Frame::Array, std::collections::BTreeSet::new()));
                expecting_key = false;
            }
            b'}' | b']' => {
                frames.pop();
                expecting_key = false;
            }
            b',' => {
                expecting_key = matches!(frames.last(), Some((Frame::Object, _)));
            }
            _ => {}
        }
        index += 1;
    }
    Ok(())
}
