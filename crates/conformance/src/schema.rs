//! A JSON Schema validator for the draft 2020-12 subset the committed
//! `schemas/*.schema.json` use (SPEC.md §30.4 "all schemas are committed and
//! exercised"): `type`, `properties`, `required`, `additionalProperties`,
//! `items`, `minItems`, `enum`, `const`, `pattern`, `minimum`, `maximum`,
//! `minLength`, `oneOf`, and `$ref` into the same document's `$defs`.
//! Any other keyword in a schema is a validation failure, so a schema cannot
//! silently rely on a constraint this validator does not check.

use serde_json::Value;

/// One validation failure: a JSON pointer and what failed there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Violation {
    /// The instance location, as a JSON pointer.
    pub at: String,
    /// What the schema demanded.
    pub message: String,
}

impl std::fmt::Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.at, self.message)
    }
}

const KNOWN_KEYWORDS: [&str; 19] = [
    "$defs",
    "$id",
    "$ref",
    "$schema",
    "additionalProperties",
    "const",
    "description",
    "enum",
    "items",
    "maximum",
    "minItems",
    "minLength",
    "minimum",
    "oneOf",
    "pattern",
    "properties",
    "required",
    "title",
    "type",
];

/// Validate `instance` against `schema` (the whole schema document, so
/// `$ref` resolves). Returns every violation found.
#[must_use]
pub fn validate(schema: &Value, instance: &Value) -> Vec<Violation> {
    let mut out = Vec::new();
    check(schema, schema, instance, "", &mut out, 0);
    out
}

fn push(out: &mut Vec<Violation>, at: &str, message: impl Into<String>) {
    out.push(Violation {
        at: if at.is_empty() {
            "/".to_owned()
        } else {
            at.to_owned()
        },
        message: message.into(),
    });
}

fn resolve<'a>(root: &'a Value, reference: &str) -> Option<&'a Value> {
    let pointer = reference.strip_prefix('#')?;
    root.pointer(pointer)
}

fn type_name(value: &Value) -> &'static str {
    match value {
        Value::Null => "null",
        Value::Bool(_) => "boolean",
        Value::Number(number) => {
            if number.is_i64() || number.is_u64() {
                "integer"
            } else {
                "number"
            }
        }
        Value::String(_) => "string",
        Value::Array(_) => "array",
        Value::Object(_) => "object",
    }
}

fn type_accepts(name: &str, actual: &str) -> bool {
    name == actual || (name == "number" && actual == "integer")
}

#[allow(clippy::too_many_lines)]
fn check(
    root: &Value,
    schema: &Value,
    instance: &Value,
    at: &str,
    out: &mut Vec<Violation>,
    depth: usize,
) {
    if depth > 64 {
        push(
            out,
            at,
            "schema nesting exceeds 64; refusing to recurse further",
        );
        return;
    }
    let Value::Object(schema_object) = schema else {
        push(out, at, "the schema node is not an object");
        return;
    };
    for keyword in schema_object.keys() {
        if !KNOWN_KEYWORDS.contains(&keyword.as_str()) {
            push(
                out,
                at,
                format!("schema keyword `{keyword}` is outside the validated subset"),
            );
        }
    }
    if let Some(Value::String(reference)) = schema_object.get("$ref") {
        match resolve(root, reference) {
            Some(target) => check(root, target, instance, at, out, depth + 1),
            None => push(out, at, format!("unresolvable $ref `{reference}`")),
        }
    }
    if let Some(expected) = schema_object.get("type") {
        let actual = type_name(instance);
        let ok = match expected {
            Value::String(name) => type_accepts(name, actual),
            Value::Array(names) => names
                .iter()
                .filter_map(Value::as_str)
                .any(|name| type_accepts(name, actual)),
            _ => false,
        };
        if !ok {
            push(out, at, format!("expected type {expected}, found {actual}"));
        }
    }
    if let Some(constant) = schema_object.get("const") {
        if constant != instance {
            push(
                out,
                at,
                format!("expected the constant {constant}, found {instance}"),
            );
        }
    }
    if let Some(Value::Array(allowed)) = schema_object.get("enum") {
        if !allowed.contains(instance) {
            push(
                out,
                at,
                format!("{instance} is not one of {}", Value::Array(allowed.clone())),
            );
        }
    }
    if let Some(Value::Array(alternatives)) = schema_object.get("oneOf") {
        let matching = alternatives
            .iter()
            .filter(|alternative| {
                let mut inner = Vec::new();
                check(root, alternative, instance, at, &mut inner, depth + 1);
                inner.is_empty()
            })
            .count();
        if matching != 1 {
            push(
                out,
                at,
                format!(
                    "oneOf: {matching} of {} alternatives match, exactly one must",
                    alternatives.len()
                ),
            );
        }
    }
    match instance {
        Value::String(text) => {
            if let Some(minimum) = schema_object.get("minLength").and_then(Value::as_u64) {
                if (text.chars().count() as u64) < minimum {
                    push(out, at, format!("string shorter than minLength {minimum}"));
                }
            }
            if let Some(Value::String(pattern)) = schema_object.get("pattern") {
                match regex_matches(pattern, text) {
                    Ok(true) => {}
                    Ok(false) => push(
                        out,
                        at,
                        format!("`{text}` does not match pattern `{pattern}`"),
                    ),
                    Err(error) => {
                        push(out, at, format!("unsupported pattern `{pattern}`: {error}"))
                    }
                }
            }
        }
        Value::Number(number) => {
            if let Some(minimum) = schema_object.get("minimum").and_then(Value::as_f64) {
                if number.as_f64().is_some_and(|value| value < minimum) {
                    push(out, at, format!("{number} is below minimum {minimum}"));
                }
            }
            if let Some(maximum) = schema_object.get("maximum").and_then(Value::as_f64) {
                if number.as_f64().is_some_and(|value| value > maximum) {
                    push(out, at, format!("{number} is above maximum {maximum}"));
                }
            }
        }
        Value::Array(items) => {
            if let Some(minimum) = schema_object.get("minItems").and_then(Value::as_u64) {
                if (items.len() as u64) < minimum {
                    push(out, at, format!("array shorter than minItems {minimum}"));
                }
            }
            if let Some(item_schema) = schema_object.get("items") {
                for (index, item) in items.iter().enumerate() {
                    check(
                        root,
                        item_schema,
                        item,
                        &format!("{at}/{index}"),
                        out,
                        depth + 1,
                    );
                }
            }
        }
        Value::Object(fields) => {
            let properties = schema_object.get("properties").and_then(Value::as_object);
            if let Some(Value::Array(required)) = schema_object.get("required") {
                for name in required.iter().filter_map(Value::as_str) {
                    if !fields.contains_key(name) {
                        push(out, at, format!("required property `{name}` is missing"));
                    }
                }
            }
            for (name, value) in fields {
                let child_at = format!("{at}/{}", name.replace('~', "~0").replace('/', "~1"));
                match properties.and_then(|map| map.get(name)) {
                    Some(property_schema) => {
                        check(root, property_schema, value, &child_at, out, depth + 1);
                    }
                    None => match schema_object.get("additionalProperties") {
                        Some(Value::Bool(false)) => {
                            push(out, &child_at, format!("property `{name}` is not allowed"));
                        }
                        Some(extra @ Value::Object(_)) => {
                            check(root, extra, value, &child_at, out, depth + 1);
                        }
                        _ => {}
                    },
                }
            }
        }
        Value::Bool(_) | Value::Null => {}
    }
}

// ---- A small anchored regex matcher for the schema patterns ----

#[derive(Debug, Clone)]
enum Atom {
    Char(char),
    Class(Vec<(char, char)>),
    Group(Vec<Node>),
}

#[derive(Debug, Clone)]
struct Node {
    atom: Atom,
    min: usize,
    max: Option<usize>,
}

fn parse_regex(pattern: &str) -> Result<Vec<Node>, String> {
    let chars: Vec<char> = pattern.chars().collect();
    if chars.len() < 2 || chars.first() != Some(&'^') || chars.last() != Some(&'$') {
        return Err("only patterns anchored with ^ and $ are supported".to_owned());
    }
    let mut position = 1usize;
    let end = chars.len() - 1;
    let nodes = parse_sequence(&chars, &mut position, end)?;
    if position != end {
        return Err("unbalanced group".to_owned());
    }
    Ok(nodes)
}

fn parse_quantifier(
    chars: &[char],
    position: &mut usize,
    end: usize,
) -> Result<(usize, Option<usize>), String> {
    Ok(match chars.get(*position) {
        Some('*') if *position < end => {
            *position += 1;
            (0, None)
        }
        Some('+') if *position < end => {
            *position += 1;
            (1, None)
        }
        Some('?') if *position < end => {
            *position += 1;
            (0, Some(1))
        }
        Some('{') if *position < end => {
            let close = chars[*position..end]
                .iter()
                .position(|c| *c == '}')
                .ok_or("unclosed quantifier")?
                + *position;
            let body: String = chars[*position + 1..close].iter().collect();
            *position = close + 1;
            let mut parts = body.splitn(2, ',');
            let low: usize = parts
                .next()
                .unwrap_or("")
                .trim()
                .parse()
                .map_err(|_| "bad quantifier")?;
            match parts.next() {
                None => (low, Some(low)),
                Some(high) if high.trim().is_empty() => (low, None),
                Some(high) => (
                    low,
                    Some(high.trim().parse().map_err(|_| "bad quantifier")?),
                ),
            }
        }
        _ => (1, Some(1)),
    })
}

fn parse_sequence(chars: &[char], position: &mut usize, end: usize) -> Result<Vec<Node>, String> {
    let mut nodes = Vec::new();
    while *position < end {
        let c = chars[*position];
        let atom = match c {
            ')' => break,
            '(' => {
                *position += 1;
                let inner = parse_sequence(chars, position, end)?;
                if chars.get(*position) != Some(&')') || *position >= end {
                    return Err("unclosed group".to_owned());
                }
                *position += 1;
                Atom::Group(inner)
            }
            '[' => {
                *position += 1;
                let mut ranges = Vec::new();
                while *position < end && chars[*position] != ']' {
                    let start = chars[*position];
                    let ranged = chars.get(*position + 1) == Some(&'-')
                        && chars.get(*position + 2).is_some_and(|c| *c != ']');
                    if ranged {
                        ranges.push((start, chars[*position + 2]));
                        *position += 3;
                    } else {
                        ranges.push((start, start));
                        *position += 1;
                    }
                }
                if *position >= end || chars[*position] != ']' {
                    return Err("unclosed class".to_owned());
                }
                *position += 1;
                Atom::Class(ranges)
            }
            '\\' => {
                let escaped = *chars.get(*position + 1).ok_or("dangling escape")?;
                *position += 2;
                Atom::Char(escaped)
            }
            '|' | '.' | '*' | '+' | '?' | '{' => {
                return Err(format!("unsupported metacharacter `{c}` at this position"));
            }
            other => {
                *position += 1;
                Atom::Char(other)
            }
        };
        let (min, max) = parse_quantifier(chars, position, end)?;
        nodes.push(Node { atom, min, max });
    }
    Ok(nodes)
}

fn atom_single(atom: &Atom, c: char) -> bool {
    match atom {
        Atom::Char(expected) => *expected == c,
        Atom::Class(ranges) => ranges.iter().any(|(low, high)| *low <= c && c <= *high),
        Atom::Group(_) => false,
    }
}

/// Match `nodes` against `input[start..]`, returning every end position.
fn match_nodes(nodes: &[Node], input: &[char], start: usize, depth: usize) -> Vec<usize> {
    if depth > 256 {
        return Vec::new();
    }
    let Some((first, rest)) = nodes.split_first() else {
        return vec![start];
    };
    let mut ends = Vec::new();
    let mut frontier = vec![start];
    let mut count = 0usize;
    loop {
        if count >= first.min {
            for position in &frontier {
                for end in match_nodes(rest, input, *position, depth + 1) {
                    if !ends.contains(&end) {
                        ends.push(end);
                    }
                }
            }
        }
        if first.max.is_some_and(|max| count >= max) || frontier.is_empty() {
            break;
        }
        let mut next = Vec::new();
        for position in &frontier {
            match &first.atom {
                Atom::Group(inner) => {
                    for end in match_nodes(inner, input, *position, depth + 1) {
                        if end > *position && !next.contains(&end) {
                            next.push(end);
                        }
                    }
                }
                single => {
                    if let Some(c) = input.get(*position) {
                        if atom_single(single, *c) && !next.contains(&(*position + 1)) {
                            next.push(*position + 1);
                        }
                    }
                }
            }
        }
        frontier = next;
        count += 1;
    }
    ends
}

/// Does `text` match the anchored `pattern`?
///
/// # Errors
///
/// A pattern outside the supported subset.
pub fn regex_matches(pattern: &str, text: &str) -> Result<bool, String> {
    let nodes = parse_regex(pattern)?;
    let input: Vec<char> = text.chars().collect();
    Ok(match_nodes(&nodes, &input, 0, 0).contains(&input.len()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_schema_patterns_match_and_reject() {
        let sixty_four = "a".repeat(64);
        let sixty_three = "a".repeat(63);
        let cases = [
            ("^LL[A-Z][0-9]{4}$", "LLL1004", true),
            ("^LL[A-Z][0-9]{4}$", "LLL100", false),
            ("^LL[A-Z][0-9]{4}$", "LLl1004", false),
            ("^[0-9a-f]{64}$", sixty_four.as_str(), true),
            ("^[0-9a-f]{64}$", sixty_three.as_str(), false),
            (
                "^[A-Z][A-Za-z0-9_]*(\\.[A-Z][A-Za-z0-9_]*)*$",
                "LexLeanExample.Main",
                true,
            ),
            (
                "^[A-Z][A-Za-z0-9_]*(\\.[A-Z][A-Za-z0-9_]*)*$",
                "LexLeanExample.main",
                false,
            ),
            (
                "^[a-z][a-z0-9-]*(\\.[a-z][a-z0-9-]*)*$",
                "lexlean.std.nat",
                true,
            ),
            (
                "^[a-z][a-z0-9-]*(\\.[a-z][a-z0-9-]*)*$",
                "lexlean..nat",
                false,
            ),
            ("^[a-z][a-z0-9-]{0,62}$", "nat-add-zero", true),
            ("^[a-z][a-z0-9-]{0,62}$", "", false),
            ("^a?b$", "b", true),
            ("^a?b$", "aab", false),
        ];
        for (pattern, text, expected) in cases {
            assert_eq!(
                regex_matches(pattern, text).expect("supported"),
                expected,
                "{pattern} vs {text:?}"
            );
        }
        assert!(
            regex_matches("a+", "aa").is_err(),
            "unanchored patterns are refused"
        );
    }

    #[test]
    fn keywords_type_required_and_additional_properties_fire() {
        let schema: Value = serde_json::json!({
            "$defs": {"hex": {"type": "string", "pattern": "^[0-9a-f]{4}$"}},
            "type": "object",
            "additionalProperties": false,
            "required": ["id", "n"],
            "properties": {
                "id": {"$ref": "#/$defs/hex"},
                "n": {"type": "integer", "minimum": 1},
                "k": {"enum": ["a", "b"]},
                "c": {"const": "fixed"},
                "list": {"type": "array", "minItems": 1, "items": {"type": "string", "minLength": 1}},
                "either": {"oneOf": [{"type": "string"}, {"type": "integer"}]}
            }
        });
        let good = serde_json::json!({"id": "beef", "n": 1, "k": "a", "c": "fixed", "list": ["x"], "either": 3});
        assert!(validate(&schema, &good).is_empty());
        let bad = serde_json::json!({"id": "beefy", "n": 0, "k": "z", "c": "loose", "list": [], "either": true, "extra": 1});
        let messages: Vec<String> = validate(&schema, &bad)
            .iter()
            .map(ToString::to_string)
            .collect();
        for expected in ["/id", "/n", "/k", "/c", "/list", "/either", "/extra"] {
            assert!(
                messages.iter().any(|m| m.starts_with(expected)),
                "{expected}: {messages:?}"
            );
        }
        let missing = serde_json::json!({});
        assert_eq!(
            validate(&schema, &missing).len(),
            2,
            "two required properties missing"
        );
        let unknown_keyword: Value = serde_json::json!({"type": "string", "format": "email"});
        assert!(!validate(&unknown_keyword, &Value::String("x".into())).is_empty());
    }
}
