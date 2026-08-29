//! Language-1.1 closed declaration, term, and proof data.
//!
//! This is a source-language IR, not Lean syntax.  Every variant has one
//! fixed Lean lowering and one fixed LaTeX rendering.  The validator is
//! deliberately conservative: unresolved or ambiguous data is rejected
//! before either backend runs.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

/// A qualified document member.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MemberRef {
    /// Imported logical module, absent for the current module.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub module: Option<String>,
    /// Declaration/member name.
    pub name: String,
}

/// Closed language-1.1 types.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[serde(deny_unknown_fields)]
pub enum SemanticType {
    /// The first universe of data types.
    Type,
    /// A declaration-bound type parameter.
    Parameter { name: String },
    /// Natural numbers.
    Nat,
    /// Booleans.
    Bool,
    /// Propositions.
    Prop,
    /// Unit.
    Unit,
    /// A list.
    List { element: Box<Self> },
    /// A document-defined type.
    Named {
        member: MemberRef,
        arguments: Vec<Self>,
    },
}

/// One explicit declaration parameter.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticParameter {
    pub name: String,
    pub r#type: SemanticType,
}

/// One ordered structure or class field.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticField {
    pub name: String,
    pub r#type: SemanticType,
}

/// One positional inductive constructor.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticConstructor {
    pub name: String,
    pub fields: Vec<SemanticType>,
}

/// One ordered record/instance assignment.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticAssignment {
    pub field: String,
    pub value: SemanticTerm,
}

/// One exhaustive match branch.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticBranch {
    pub constructor: MemberRef,
    pub binders: Vec<String>,
    pub body: SemanticTerm,
}

/// Closed language-1.1 terms.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[serde(deny_unknown_fields)]
pub enum SemanticTerm {
    Var {
        name: String,
    },
    Nat {
        value: String,
    },
    Bool {
        value: bool,
    },
    Unit,
    Nil {
        element: SemanticType,
    },
    Cons {
        head: Box<Self>,
        tail: Box<Self>,
    },
    Record {
        r#type: MemberRef,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        type_arguments: Vec<SemanticType>,
        fields: Vec<SemanticAssignment>,
    },
    Constructor {
        constructor: MemberRef,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        type_arguments: Vec<SemanticType>,
        arguments: Vec<Self>,
    },
    /// A deterministically resolved explicit document instance value.
    InstanceValue {
        class: MemberRef,
        arguments: Vec<SemanticType>,
        resolved: MemberRef,
    },
    Project {
        value: Box<Self>,
        field: String,
    },
    Call {
        function: MemberRef,
        arguments: Vec<Self>,
    },
    If {
        condition: Box<Self>,
        then_value: Box<Self>,
        else_value: Box<Self>,
    },
    Match {
        scrutinee: Box<Self>,
        branches: Vec<SemanticBranch>,
    },
    Eq {
        left: Box<Self>,
        right: Box<Self>,
    },
    Le {
        left: Box<Self>,
        right: Box<Self>,
    },
    Lt {
        left: Box<Self>,
        right: Box<Self>,
    },
    Add {
        left: Box<Self>,
        right: Box<Self>,
    },
    Beq {
        left: Box<Self>,
        right: Box<Self>,
    },
    Ble {
        left: Box<Self>,
        right: Box<Self>,
    },
    Blt {
        left: Box<Self>,
        right: Box<Self>,
    },
    And {
        left: Box<Self>,
        right: Box<Self>,
    },
    /// Propositional conjunction, distinct from Boolean conjunction.
    PropAnd {
        left: Box<Self>,
        right: Box<Self>,
    },
    Or {
        left: Box<Self>,
        right: Box<Self>,
    },
    Not {
        value: Box<Self>,
    },
    Implies {
        premise: Box<Self>,
        conclusion: Box<Self>,
    },
    Iff {
        left: Box<Self>,
        right: Box<Self>,
    },
    Forall {
        binder: SemanticParameter,
        body: Box<Self>,
    },
}

/// One proof branch for a fixed cases/induction lowering.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticProofBranch {
    pub constructor: String,
    pub binders: Vec<String>,
    pub proof: Box<SemanticProof>,
}

/// A fixed Boolean comparison reflected into a proposition without using
/// propositional extensionality.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SemanticReflectionComparison {
    NatBeq,
    NatBlt,
}

/// One Nat-valued record projection and its canonical expected literal.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticReflectionField {
    pub field: String,
    pub expected: String,
}

/// Closed, axiom-free Boolean reflection proof shapes.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[serde(deny_unknown_fields)]
pub enum SemanticReflection {
    /// Structural reflection for a Nat-indexed list validator/predicate pair.
    List {
        parameter: String,
        values: String,
        boolean_definition: MemberRef,
        proposition_definition: MemberRef,
        comparison: SemanticReflectionComparison,
    },
    /// Reflection for a finite right-associated conjunction of Nat record
    /// field comparisons.
    Record {
        record: String,
        boolean_definition: MemberRef,
        proposition_definition: MemberRef,
        fields: Vec<SemanticReflectionField>,
    },
}

/// Closed language-1.1 proof forms.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[serde(deny_unknown_fields)]
pub enum SemanticProof {
    Reflexivity,
    Decide,
    Simplify {
        definitions: Vec<MemberRef>,
    },
    Constructor {
        branches: Vec<Self>,
    },
    Cases {
        scrutinee: String,
        branches: Vec<SemanticProofBranch>,
    },
    Induction {
        scrutinee: String,
        /// Other theorem parameters generalized before structural induction.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        generalizing: Vec<String>,
        branches: Vec<SemanticProofBranch>,
    },
    Congruence,
    /// A fixed natural-deduction bridge from executable Boolean validation to
    /// an independent proposition. The backend never invokes `propext`.
    BooleanReflection {
        reflection: SemanticReflection,
    },
    /// Exact application of one prior theorem to checked semantic arguments.
    Apply {
        theorem: MemberRef,
        arguments: Vec<SemanticTerm>,
    },
}

/// A closed declaration.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[serde(deny_unknown_fields)]
pub enum SemanticDeclaration {
    Structure {
        name: String,
        type_parameters: Vec<String>,
        parameters: Vec<SemanticParameter>,
        fields: Vec<SemanticField>,
    },
    Class {
        name: String,
        type_parameters: Vec<String>,
        parameters: Vec<SemanticParameter>,
        fields: Vec<SemanticField>,
    },
    Instance {
        name: String,
        class: MemberRef,
        arguments: Vec<SemanticType>,
        priority: u64,
        fields: Vec<SemanticAssignment>,
    },
    Inductive {
        name: String,
        type_parameters: Vec<String>,
        parameters: Vec<SemanticParameter>,
        constructors: Vec<SemanticConstructor>,
    },
    Definition {
        name: String,
        parameters: Vec<SemanticParameter>,
        result: SemanticType,
        #[serde(skip_serializing_if = "Option::is_none")]
        recursive_argument: Option<String>,
        body: SemanticTerm,
    },
    Theorem {
        name: String,
        parameters: Vec<SemanticParameter>,
        statement: SemanticTerm,
        proof: SemanticProof,
        /// Exact, sorted axiom set. Omission means the empty policy.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        axioms: Vec<String>,
    },
}

impl SemanticDeclaration {
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::Structure { name, .. }
            | Self::Class { name, .. }
            | Self::Instance { name, .. }
            | Self::Inductive { name, .. }
            | Self::Definition { name, .. }
            | Self::Theorem { name, .. } => name,
        }
    }

    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Structure { .. } => "structure",
            Self::Class { .. } => "class",
            Self::Instance { .. } => "instance",
            Self::Inductive { .. } => "inductive",
            Self::Definition { .. } => "definition",
            Self::Theorem { .. } => "theorem",
        }
    }

    #[must_use]
    pub fn axioms(&self) -> &[String] {
        match self {
            Self::Theorem { axioms, .. } => axioms,
            _ => &[],
        }
    }

    #[must_use]
    pub fn axiom_policy_kind(&self) -> &'static str {
        if self.axioms().is_empty() {
            "none"
        } else {
            "exact"
        }
    }
}

/// A complete high-level semantic module.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticModule {
    pub spec: String,
    pub declarations: Vec<SemanticDeclaration>,
}

#[derive(Default)]
struct Environment<'a> {
    imports: &'a [String],
    types: BTreeMap<String, TypeInfo>,
    functions: BTreeMap<String, FunctionInfo>,
    instances: BTreeMap<String, MemberRef>,
    proof_rules: BTreeMap<String, Vec<SemanticType>>,
}

#[derive(Clone)]
struct TypeInfo {
    parameters: usize,
    fields: Vec<String>,
    constructors: BTreeMap<String, usize>,
    type_parameters: Vec<String>,
    field_types: Vec<SemanticType>,
    constructor_types: BTreeMap<String, Vec<SemanticType>>,
    class: bool,
}

#[derive(Clone)]
struct FunctionInfo {
    parameters: Vec<SemanticType>,
    result: SemanticType,
}

fn member_key(member: &MemberRef) -> String {
    match &member.module {
        Some(module) => format!("{module}::{}", member.name),
        None => member.name.clone(),
    }
}

fn member_from_key(key: &str) -> MemberRef {
    match key.split_once("::") {
        Some((module, name)) => MemberRef {
            module: Some(module.to_owned()),
            name: name.to_owned(),
        },
        None => MemberRef {
            module: None,
            name: key.to_owned(),
        },
    }
}

fn qualify_type(ty: &SemanticType, module: &str) -> SemanticType {
    match ty {
        SemanticType::Named { member, arguments } => SemanticType::Named {
            member: MemberRef {
                module: member.module.clone().or_else(|| Some(module.to_owned())),
                name: member.name.clone(),
            },
            arguments: arguments
                .iter()
                .map(|argument| qualify_type(argument, module))
                .collect(),
        },
        SemanticType::List { element } => SemanticType::List {
            element: Box::new(qualify_type(element, module)),
        },
        other => other.clone(),
    }
}

fn type_info<'a>(member: &MemberRef, env: &'a Environment<'_>) -> Option<&'a TypeInfo> {
    env.types.get(&member_key(member))
}

fn function_info<'a>(member: &MemberRef, env: &'a Environment<'_>) -> Option<&'a FunctionInfo> {
    env.functions.get(&member_key(member))
}

fn legal_name(name: &str) -> bool {
    let mut segments = name.split('.');
    segments.all(|segment| {
        let mut chars = segment.chars();
        chars
            .next()
            .is_some_and(|first| first.is_ascii_alphabetic())
            && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
            && !matches!(
                segment,
                "axiom"
                    | "opaque"
                    | "partial"
                    | "unsafe"
                    | "noncomputable"
                    | "termination_by"
                    | "sorry"
                    | "admit"
            )
    })
}

fn check_name(name: &str, what: &str) -> Result<(), String> {
    if legal_name(name) {
        Ok(())
    } else {
        Err(format!("invalid {what} name `{name}`"))
    }
}

fn check_member(member: &MemberRef, env: &Environment<'_>) -> Result<(), String> {
    check_name(&member.name, "member")?;
    if let Some(module) = &member.module {
        check_name(module, "module")?;
        if !env.imports.contains(module) {
            return Err(format!(
                "forward or unavailable module reference `{module}`"
            ));
        }
    }
    Ok(())
}

fn check_type(ty: &SemanticType, env: &Environment<'_>) -> Result<(), String> {
    match ty {
        SemanticType::Type
        | SemanticType::Parameter { .. }
        | SemanticType::Nat
        | SemanticType::Bool
        | SemanticType::Prop
        | SemanticType::Unit => Ok(()),
        SemanticType::List { element } => check_type(element, env),
        SemanticType::Named { member, arguments } => {
            check_member(member, env)?;
            for argument in arguments {
                check_type(argument, env)?;
            }
            let info = type_info(member, env)
                .ok_or_else(|| format!("forward or missing type `{}`", member_key(member)))?;
            if info.parameters != arguments.len() {
                return Err(format!(
                    "type `{}` expects {} argument(s), received {}",
                    member_key(member),
                    info.parameters,
                    arguments.len()
                ));
            }
            Ok(())
        }
    }
}

fn check_type_parameters(ty: &SemanticType, allowed: &BTreeSet<String>) -> Result<(), String> {
    match ty {
        SemanticType::Parameter { name } => {
            check_name(name, "type parameter")?;
            if allowed.contains(name) {
                Ok(())
            } else {
                Err(format!("unbound type parameter `{name}`"))
            }
        }
        SemanticType::List { element } => check_type_parameters(element, allowed),
        SemanticType::Named { arguments, .. } => {
            for argument in arguments {
                check_type_parameters(argument, allowed)?;
            }
            Ok(())
        }
        SemanticType::Type
        | SemanticType::Nat
        | SemanticType::Bool
        | SemanticType::Prop
        | SemanticType::Unit => Ok(()),
    }
}

fn type_parameter_set(parameters: &[String]) -> Result<BTreeSet<String>, String> {
    let mut out = BTreeSet::new();
    for parameter in parameters {
        check_name(parameter, "type parameter")?;
        if !out.insert(parameter.clone()) {
            return Err(format!("duplicate type parameter `{parameter}`"));
        }
    }
    Ok(out)
}

fn is_structural_domain(ty: &SemanticType, env: &Environment<'_>) -> bool {
    match ty {
        SemanticType::Nat | SemanticType::List { .. } => true,
        SemanticType::Named { member, .. } => type_info(member, env)
            .is_some_and(|info| !info.constructors.is_empty() && info.fields.is_empty()),
        _ => false,
    }
}

fn check_parameters(
    parameters: &[SemanticParameter],
    env: &Environment<'_>,
    type_parameters: &BTreeSet<String>,
) -> Result<BTreeSet<String>, String> {
    let mut names = BTreeSet::new();
    for parameter in parameters {
        check_name(&parameter.name, "parameter")?;
        check_type(&parameter.r#type, env)?;
        check_type_parameters(&parameter.r#type, type_parameters)?;
        if !names.insert(parameter.name.clone()) {
            return Err(format!("duplicate parameter `{}`", parameter.name));
        }
    }
    Ok(names)
}

fn typed_locals(parameters: &[SemanticParameter]) -> BTreeMap<String, SemanticType> {
    parameters
        .iter()
        .map(|parameter| (parameter.name.clone(), parameter.r#type.clone()))
        .collect()
}

fn check_assignments(
    assignments: &[SemanticAssignment],
    expected: &[String],
    locals: &BTreeSet<String>,
    env: &Environment<'_>,
    recursion: Option<(&str, usize, &str)>,
    smaller: &BTreeSet<String>,
) -> Result<(), String> {
    let observed: Vec<String> = assignments.iter().map(|row| row.field.clone()).collect();
    if observed != expected {
        return Err(format!(
            "fields are not the exact ordered set: expected {expected:?}, observed {observed:?}"
        ));
    }
    for assignment in assignments {
        check_name(&assignment.field, "field")?;
        check_term(&assignment.value, locals, env, recursion, smaller)?;
    }
    Ok(())
}

fn constructor_arity(member: &MemberRef, env: &Environment<'_>) -> Option<usize> {
    env.types.iter().find_map(|(owner, info)| {
        (member_from_key(owner).module == member.module)
            .then(|| info.constructors.get(&member.name).copied())
            .flatten()
    })
}

#[allow(clippy::too_many_lines)]
fn check_term(
    term: &SemanticTerm,
    locals: &BTreeSet<String>,
    env: &Environment<'_>,
    recursion: Option<(&str, usize, &str)>,
    smaller: &BTreeSet<String>,
) -> Result<(), String> {
    let pair = |left: &SemanticTerm, right: &SemanticTerm| {
        check_term(left, locals, env, recursion, smaller)?;
        check_term(right, locals, env, recursion, smaller)
    };
    match term {
        SemanticTerm::Var { name } => {
            if locals.contains(name) {
                Ok(())
            } else {
                Err(format!("unbound local `{name}`"))
            }
        }
        SemanticTerm::Nat { value } => {
            if value == "0"
                || (value.bytes().all(|b| b.is_ascii_digit()) && !value.starts_with('0'))
            {
                Ok(())
            } else {
                Err(format!("noncanonical natural literal `{value}`"))
            }
        }
        SemanticTerm::Bool { .. } | SemanticTerm::Unit => Ok(()),
        SemanticTerm::Nil { element } => check_type(element, env),
        SemanticTerm::Cons { head, tail }
        | SemanticTerm::Eq {
            left: head,
            right: tail,
        }
        | SemanticTerm::Le {
            left: head,
            right: tail,
        }
        | SemanticTerm::Lt {
            left: head,
            right: tail,
        }
        | SemanticTerm::Add {
            left: head,
            right: tail,
        }
        | SemanticTerm::Beq {
            left: head,
            right: tail,
        }
        | SemanticTerm::Ble {
            left: head,
            right: tail,
        }
        | SemanticTerm::Blt {
            left: head,
            right: tail,
        }
        | SemanticTerm::And {
            left: head,
            right: tail,
        }
        | SemanticTerm::PropAnd {
            left: head,
            right: tail,
        }
        | SemanticTerm::Or {
            left: head,
            right: tail,
        }
        | SemanticTerm::Implies {
            premise: head,
            conclusion: tail,
        }
        | SemanticTerm::Iff {
            left: head,
            right: tail,
        } => pair(head, tail),
        SemanticTerm::Not { value } | SemanticTerm::Project { value, .. } => {
            check_term(value, locals, env, recursion, smaller)
        }
        SemanticTerm::Record {
            r#type,
            type_arguments,
            fields,
        } => {
            check_member(r#type, env)?;
            for argument in type_arguments {
                check_type(argument, env)?;
            }
            let info = type_info(r#type, env)
                .ok_or_else(|| format!("record type `{}` is unavailable", member_key(r#type)))?;
            if info.parameters != type_arguments.len() {
                return Err(format!(
                    "record type `{}` expects {} type argument(s), received {}",
                    r#type.name,
                    info.parameters,
                    type_arguments.len()
                ));
            }
            check_assignments(fields, &info.fields, locals, env, recursion, smaller)
        }
        SemanticTerm::Constructor {
            constructor,
            type_arguments,
            arguments,
        } => {
            check_member(constructor, env)?;
            for argument in type_arguments {
                check_type(argument, env)?;
            }
            for argument in arguments {
                check_term(argument, locals, env, recursion, smaller)?;
            }
            if let Some(arity) = constructor_arity(constructor, env) {
                if arity != arguments.len() {
                    return Err(format!(
                        "constructor `{}` expects {arity} argument(s), received {}",
                        constructor.name,
                        arguments.len()
                    ));
                }
            } else if constructor.module.is_none()
                && !matches!(
                    constructor.name.as_str(),
                    "List.nil" | "List.cons" | "Nat.zero" | "Nat.succ"
                )
            {
                return Err(format!("unknown constructor `{}`", constructor.name));
            }
            Ok(())
        }
        SemanticTerm::InstanceValue {
            class,
            arguments,
            resolved,
        } => {
            check_member(class, env)?;
            check_name(&resolved.name, "resolved instance")?;
            if resolved
                .module
                .as_ref()
                .is_some_and(|module| !env.imports.contains(module))
            {
                return Err(format!(
                    "resolved instance `{}` is outside the imported module closure",
                    member_key(resolved)
                ));
            }
            for argument in arguments {
                check_type(argument, env)?;
            }
            let key = format!("{}:{arguments:?}", member_key(class));
            match env.instances.get(&key) {
                Some(instance) if instance == resolved => Ok(()),
                Some(instance) => Err(format!(
                    "instance requirement `{key}` resolves to `{}`, not `{}`",
                    member_key(instance),
                    member_key(resolved)
                )),
                None => Err(format!("missing instance for requirement `{key}`")),
            }
        }
        SemanticTerm::Call {
            function,
            arguments,
        } => {
            check_member(function, env)?;
            for argument in arguments {
                check_term(argument, locals, env, recursion, smaller)?;
            }
            let recursive_call = if function.module.is_none() {
                recursion.filter(|(name, _, _)| *name == function.name)
            } else {
                None
            };
            if let Some((self_name, decreasing, _)) = recursive_call {
                if arguments.len() <= decreasing {
                    return Err(format!(
                        "recursive call `{self_name}` omits its decreasing argument"
                    ));
                }
                match &arguments[decreasing] {
                    SemanticTerm::Var { name } if smaller.contains(name) => {}
                    _ => {
                        return Err(format!(
                            "recursive call `{self_name}` is not on a structurally smaller value"
                        ));
                    }
                }
            } else {
                let info = function_info(function, env).ok_or_else(|| {
                    format!("forward or missing function `{}`", member_key(function))
                })?;
                if info.parameters.len() != arguments.len() {
                    return Err(format!(
                        "function `{}` expects {} argument(s), received {}",
                        member_key(function),
                        info.parameters.len(),
                        arguments.len()
                    ));
                }
            }
            Ok(())
        }
        SemanticTerm::If {
            condition,
            then_value,
            else_value,
        } => {
            check_term(condition, locals, env, recursion, smaller)?;
            pair(then_value, else_value)
        }
        SemanticTerm::Match {
            scrutinee,
            branches,
        } => {
            check_term(scrutinee, locals, env, recursion, smaller)?;
            if branches.is_empty() {
                return Err("match has no branches".to_owned());
            }
            let mut constructors = BTreeSet::new();
            for branch in branches {
                check_member(&branch.constructor, env)?;
                if !constructors.insert(branch.constructor.name.clone()) {
                    return Err(format!(
                        "duplicate match branch `{}`",
                        branch.constructor.name
                    ));
                }
                let expected = match branch.constructor.name.as_str() {
                    "List.nil" | "Nat.zero" => 0,
                    "List.cons" => 2,
                    "Nat.succ" => 1,
                    _ => constructor_arity(&branch.constructor, env).ok_or_else(|| {
                        format!("unknown match constructor `{}`", branch.constructor.name)
                    })?,
                };
                if expected != branch.binders.len() {
                    return Err(format!(
                        "match branch `{}` expects {expected} binder(s), received {}",
                        branch.constructor.name,
                        branch.binders.len()
                    ));
                }
                let mut branch_locals = locals.clone();
                for binder in &branch.binders {
                    check_name(binder, "pattern binder")?;
                    if !branch_locals.insert(binder.clone()) {
                        return Err(format!("duplicate or shadowed pattern binder `{binder}`"));
                    }
                }
                let mut branch_smaller = smaller.clone();
                if recursion.is_some_and(|(_, _, argument)| {
                    matches!(scrutinee.as_ref(), SemanticTerm::Var { name } if name == argument)
                }) {
                    if let Some(last) = branch.binders.last() {
                        branch_smaller.insert(last.clone());
                    }
                }
                check_term(
                    &branch.body,
                    &branch_locals,
                    env,
                    recursion,
                    &branch_smaller,
                )?;
            }
            let list = BTreeSet::from(["List.cons".to_owned(), "List.nil".to_owned()]);
            let nat = BTreeSet::from(["Nat.succ".to_owned(), "Nat.zero".to_owned()]);
            let declared = env.types.values().find_map(|info| {
                let set: BTreeSet<String> = info.constructors.keys().cloned().collect();
                (set == constructors).then_some(set)
            });
            if constructors != list && constructors != nat && declared.is_none() {
                return Err(format!(
                    "nonexhaustive or mixed match branches {constructors:?}"
                ));
            }
            Ok(())
        }
        SemanticTerm::Forall { binder, body } => {
            check_name(&binder.name, "binder")?;
            check_type(&binder.r#type, env)?;
            let mut nested = locals.clone();
            if !nested.insert(binder.name.clone()) {
                return Err(format!("shadowed binder `{}`", binder.name));
            }
            check_term(body, &nested, env, recursion, smaller)
        }
    }
}

fn substitute_type(
    ty: &SemanticType,
    substitutions: &BTreeMap<String, SemanticType>,
) -> SemanticType {
    match ty {
        SemanticType::Parameter { name } => substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        SemanticType::List { element } => SemanticType::List {
            element: Box::new(substitute_type(element, substitutions)),
        },
        SemanticType::Named { member, arguments } => SemanticType::Named {
            member: member.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_type(argument, substitutions))
                .collect(),
        },
        _ => ty.clone(),
    }
}

fn substitutions(info: &TypeInfo, arguments: &[SemanticType]) -> BTreeMap<String, SemanticType> {
    info.type_parameters
        .iter()
        .cloned()
        .zip(arguments.iter().cloned())
        .collect()
}

fn require_type(
    observed: Option<SemanticType>,
    expected: &SemanticType,
    context: &str,
) -> Result<(), String> {
    if let Some(observed) = observed {
        if &observed != expected {
            return Err(format!(
                "{context} has type {observed:?}, expected {expected:?}"
            ));
        }
    }
    Ok(())
}

fn same_type(
    left: Option<SemanticType>,
    right: Option<SemanticType>,
    context: &str,
) -> Result<Option<SemanticType>, String> {
    match (left, right) {
        (Some(left), Some(right)) if left != right => Err(format!(
            "{context} has incompatible types {left:?} and {right:?}"
        )),
        (Some(left), _) => Ok(Some(left)),
        (_, Some(right)) => Ok(Some(right)),
        (None, None) => Ok(None),
    }
}

fn constructor_signature(
    constructor: &MemberRef,
    type_arguments: &[SemanticType],
    env: &Environment<'_>,
) -> Result<Option<(SemanticType, Vec<SemanticType>)>, String> {
    if constructor.module.is_none()
        && (constructor.name == "List.nil" || constructor.name == "List.cons")
    {
        let [element] = type_arguments else {
            return Err(format!(
                "constructor `{}` requires one explicit type argument",
                constructor.name
            ));
        };
        let list = SemanticType::List {
            element: Box::new(element.clone()),
        };
        let fields = if constructor.name == "List.cons" {
            vec![element.clone(), list.clone()]
        } else {
            Vec::new()
        };
        return Ok(Some((list, fields)));
    }
    if constructor.module.is_none()
        && (constructor.name == "Nat.zero" || constructor.name == "Nat.succ")
    {
        if !type_arguments.is_empty() {
            return Err(format!(
                "constructor `{}` takes no type arguments",
                constructor.name
            ));
        }
        let fields = if constructor.name == "Nat.succ" {
            vec![SemanticType::Nat]
        } else {
            Vec::new()
        };
        return Ok(Some((SemanticType::Nat, fields)));
    }
    for (owner, info) in &env.types {
        let owner_member = member_from_key(owner);
        if owner_member.module != constructor.module {
            continue;
        }
        if let Some(fields) = info.constructor_types.get(&constructor.name) {
            if info.parameters != type_arguments.len() {
                return Err(format!(
                    "constructor `{}` expects {} type argument(s), received {}",
                    constructor.name,
                    info.parameters,
                    type_arguments.len()
                ));
            }
            let map = substitutions(info, type_arguments);
            let result = SemanticType::Named {
                member: owner_member,
                arguments: type_arguments.to_vec(),
            };
            return Ok(Some((
                result,
                fields
                    .iter()
                    .map(|field| substitute_type(field, &map))
                    .collect(),
            )));
        }
    }
    Ok(None)
}

#[allow(clippy::too_many_lines)]
fn infer_term(
    term: &SemanticTerm,
    locals: &BTreeMap<String, SemanticType>,
    env: &Environment<'_>,
) -> Result<Option<SemanticType>, String> {
    let infer = |term| infer_term(term, locals, env);
    match term {
        SemanticTerm::Var { name } => locals
            .get(name)
            .cloned()
            .map(Some)
            .ok_or_else(|| format!("unbound typed local `{name}`")),
        SemanticTerm::Nat { .. } => Ok(Some(SemanticType::Nat)),
        SemanticTerm::Bool { .. } => Ok(Some(SemanticType::Bool)),
        SemanticTerm::Unit => Ok(Some(SemanticType::Unit)),
        SemanticTerm::Nil { element } => Ok(Some(SemanticType::List {
            element: Box::new(element.clone()),
        })),
        SemanticTerm::Cons { head, tail } => {
            let head = infer(head)?;
            let tail = infer(tail)?;
            match tail {
                Some(SemanticType::List { element }) => {
                    require_type(head, &element, "list head")?;
                    Ok(Some(SemanticType::List { element }))
                }
                Some(other) => Err(format!("list tail has non-list type {other:?}")),
                None => Ok(None),
            }
        }
        SemanticTerm::Record {
            r#type,
            type_arguments,
            fields,
        } => {
            let info = type_info(r#type, env)
                .ok_or_else(|| format!("missing record type `{}`", member_key(r#type)))?;
            let map = substitutions(info, type_arguments);
            for (assignment, expected) in fields.iter().zip(&info.field_types) {
                require_type(
                    infer(&assignment.value)?,
                    &substitute_type(expected, &map),
                    &format!("record field `{}.{}`", r#type.name, assignment.field),
                )?;
            }
            Ok(Some(SemanticType::Named {
                member: r#type.clone(),
                arguments: type_arguments.clone(),
            }))
        }
        SemanticTerm::Constructor {
            constructor,
            type_arguments,
            arguments,
        } => {
            let Some((result, expected)) = constructor_signature(constructor, type_arguments, env)?
            else {
                return Ok(None);
            };
            for (argument, expected) in arguments.iter().zip(expected) {
                require_type(
                    infer(argument)?,
                    &expected,
                    &format!("constructor `{}` argument", constructor.name),
                )?;
            }
            Ok(Some(result))
        }
        SemanticTerm::InstanceValue {
            class,
            arguments,
            resolved,
        } => {
            let key = format!("{}:{arguments:?}", member_key(class));
            match env.instances.get(&key) {
                Some(instance) if instance == resolved => Ok(Some(SemanticType::Named {
                    member: class.clone(),
                    arguments: arguments.clone(),
                })),
                Some(instance) => Err(format!(
                    "instance requirement `{key}` resolves to `{}`, not `{}`",
                    member_key(instance),
                    member_key(resolved)
                )),
                None => Err(format!("missing instance for requirement `{key}`")),
            }
        }
        SemanticTerm::Project { value, field } => {
            let Some(SemanticType::Named { member, arguments }) = infer(value)? else {
                return Err(format!(
                    "projection `.{field}` requires a known record value"
                ));
            };
            let info = type_info(&member, env)
                .ok_or_else(|| format!("projection owner `{}` is missing", member_key(&member)))?;
            let index = info
                .fields
                .iter()
                .position(|candidate| candidate == field)
                .ok_or_else(|| format!("record `{}` has no field `{field}`", member.name))?;
            Ok(Some(substitute_type(
                &info.field_types[index],
                &substitutions(info, &arguments),
            )))
        }
        SemanticTerm::Call {
            function,
            arguments,
        } => {
            let info = function_info(function, env)
                .ok_or_else(|| format!("missing typed function `{}`", member_key(function)))?;
            for (argument, expected) in arguments.iter().zip(&info.parameters) {
                require_type(
                    infer(argument)?,
                    expected,
                    &format!("function `{}` argument", function.name),
                )?;
            }
            Ok(Some(info.result.clone()))
        }
        SemanticTerm::If {
            condition,
            then_value,
            else_value,
        } => {
            require_type(infer(condition)?, &SemanticType::Bool, "if condition")?;
            same_type(infer(then_value)?, infer(else_value)?, "if branches")
        }
        SemanticTerm::Match {
            scrutinee,
            branches,
        } => {
            let scrutinee_type = infer(scrutinee)?;
            let mut result = None;
            for branch in branches {
                let mut branch_locals = locals.clone();
                let binder_types = match &scrutinee_type {
                    Some(SemanticType::List { element }) => {
                        match branch.constructor.name.as_str() {
                            "List.nil" => Vec::new(),
                            "List.cons" => vec![
                                element.as_ref().clone(),
                                SemanticType::List {
                                    element: element.clone(),
                                },
                            ],
                            _ => return Err("list match uses a non-list constructor".to_owned()),
                        }
                    }
                    Some(SemanticType::Nat) => match branch.constructor.name.as_str() {
                        "Nat.zero" => Vec::new(),
                        "Nat.succ" => vec![SemanticType::Nat],
                        _ => return Err("Nat match uses a non-Nat constructor".to_owned()),
                    },
                    Some(SemanticType::Named { member, arguments }) => {
                        let Some((owner, fields)) =
                            constructor_signature(&branch.constructor, arguments, env)?
                        else {
                            return Err(format!(
                                "unknown match constructor `{}`",
                                branch.constructor.name
                            ));
                        };
                        let expected_owner = SemanticType::Named {
                            member: member.clone(),
                            arguments: arguments.clone(),
                        };
                        require_type(Some(owner), &expected_owner, "match constructor")?;
                        fields
                    }
                    Some(other) => {
                        return Err(format!("cannot pattern match value of type {other:?}"));
                    }
                    None => return Ok(None),
                };
                for (binder, binder_type) in branch.binders.iter().zip(binder_types) {
                    branch_locals.insert(binder.clone(), binder_type);
                }
                result = same_type(
                    result,
                    infer_term(&branch.body, &branch_locals, env)?,
                    "match branches",
                )?;
            }
            Ok(result)
        }
        SemanticTerm::Eq { left, right } => {
            let _ = same_type(infer(left)?, infer(right)?, "equality operands")?;
            Ok(Some(SemanticType::Prop))
        }
        SemanticTerm::Le { left, right } | SemanticTerm::Lt { left, right } => {
            require_type(infer(left)?, &SemanticType::Nat, "order left operand")?;
            require_type(infer(right)?, &SemanticType::Nat, "order right operand")?;
            Ok(Some(SemanticType::Prop))
        }
        SemanticTerm::Add { left, right } => {
            require_type(infer(left)?, &SemanticType::Nat, "addition left operand")?;
            require_type(infer(right)?, &SemanticType::Nat, "addition right operand")?;
            Ok(Some(SemanticType::Nat))
        }
        SemanticTerm::Beq { left, right }
        | SemanticTerm::Ble { left, right }
        | SemanticTerm::Blt { left, right } => {
            require_type(
                infer(left)?,
                &SemanticType::Nat,
                "Boolean comparison left operand",
            )?;
            require_type(
                infer(right)?,
                &SemanticType::Nat,
                "Boolean comparison right operand",
            )?;
            Ok(Some(SemanticType::Bool))
        }
        SemanticTerm::And { left, right } | SemanticTerm::Or { left, right } => {
            require_type(
                infer(left)?,
                &SemanticType::Bool,
                "Boolean connective left operand",
            )?;
            require_type(
                infer(right)?,
                &SemanticType::Bool,
                "Boolean connective right operand",
            )?;
            Ok(Some(SemanticType::Bool))
        }
        SemanticTerm::PropAnd { left, right } => {
            require_type(
                infer(left)?,
                &SemanticType::Prop,
                "propositional conjunction left operand",
            )?;
            require_type(
                infer(right)?,
                &SemanticType::Prop,
                "propositional conjunction right operand",
            )?;
            Ok(Some(SemanticType::Prop))
        }
        SemanticTerm::Not { value } => {
            require_type(
                infer(value)?,
                &SemanticType::Bool,
                "Boolean negation operand",
            )?;
            Ok(Some(SemanticType::Bool))
        }
        SemanticTerm::Implies {
            premise,
            conclusion,
        }
        | SemanticTerm::Iff {
            left: premise,
            right: conclusion,
        } => {
            require_type(
                infer(premise)?,
                &SemanticType::Prop,
                "proposition left operand",
            )?;
            require_type(
                infer(conclusion)?,
                &SemanticType::Prop,
                "proposition right operand",
            )?;
            Ok(Some(SemanticType::Prop))
        }
        SemanticTerm::Forall { binder, body } => {
            let mut nested = locals.clone();
            nested.insert(binder.name.clone(), binder.r#type.clone());
            require_type(
                infer_term(body, &nested, env)?,
                &SemanticType::Prop,
                "forall body",
            )?;
            Ok(Some(SemanticType::Prop))
        }
    }
}

fn check_proof(
    proof: &SemanticProof,
    locals: &BTreeMap<String, SemanticType>,
    env: &Environment<'_>,
) -> Result<(), String> {
    match proof {
        SemanticProof::Reflexivity | SemanticProof::Decide | SemanticProof::Congruence => Ok(()),
        SemanticProof::BooleanReflection { reflection } => {
            check_boolean_reflection(reflection, locals, env)
        }
        SemanticProof::Apply { theorem, arguments } => {
            check_member(theorem, env)?;
            let parameters = env.proof_rules.get(&member_key(theorem)).ok_or_else(|| {
                format!(
                    "proof application names a forward or missing theorem `{}`",
                    member_key(theorem)
                )
            })?;
            if parameters.len() != arguments.len() {
                return Err(format!(
                    "theorem `{}` expects {} argument(s), received {}",
                    member_key(theorem),
                    parameters.len(),
                    arguments.len()
                ));
            }
            let local_names = locals.keys().cloned().collect();
            for (argument, expected) in arguments.iter().zip(parameters) {
                check_term(argument, &local_names, env, None, &BTreeSet::new())?;
                require_type(
                    infer_term(argument, locals, env)?,
                    expected,
                    "theorem application argument",
                )?;
            }
            Ok(())
        }
        SemanticProof::Simplify { definitions } => {
            if definitions.is_empty() {
                return Err("simplify requires at least one named definition".to_owned());
            }
            let mut previous = None;
            for definition in definitions {
                check_member(definition, env)?;
                let builtin_bridge = definition.module.is_none()
                    && matches!(
                        definition.name.as_str(),
                        "Bool.and_eq_true" | "Nat.beq_eq" | "Nat.blt_eq"
                    );
                let local_hypothesis = definition.module.is_none()
                    && locals.get(&definition.name) == Some(&SemanticType::Prop);
                if function_info(definition, env).is_none()
                    && !env.proof_rules.contains_key(&member_key(definition))
                    && !builtin_bridge
                    && !local_hypothesis
                {
                    return Err(format!(
                        "simplify names a forward or missing definition `{}`",
                        member_key(definition)
                    ));
                }
                if previous.is_some_and(|prior: &MemberRef| prior >= definition) {
                    return Err("simplify definitions are strictly sorted and unique".to_owned());
                }
                previous = Some(definition);
            }
            Ok(())
        }
        SemanticProof::Constructor { branches } => {
            if branches.is_empty() {
                return Err("constructor proof requires branches".to_owned());
            }
            for branch in branches {
                check_proof(branch, locals, env)?;
            }
            Ok(())
        }
        SemanticProof::Cases {
            scrutinee,
            branches,
        } => check_elimination_proof(scrutinee, branches, false, locals, env),
        SemanticProof::Induction {
            scrutinee,
            generalizing,
            branches,
        } => {
            let mut previous = None;
            for name in generalizing {
                check_name(name, "generalized proof binder")?;
                if name == scrutinee || !locals.contains_key(name) {
                    return Err(format!(
                        "generalized proof binder `{name}` is absent or is the scrutinee"
                    ));
                }
                if previous.is_some_and(|prior: &String| prior >= name) {
                    return Err(
                        "generalized proof binders are strictly sorted and unique".to_owned()
                    );
                }
                previous = Some(name);
            }
            check_elimination_proof(scrutinee, branches, true, locals, env)
        }
    }
}

fn check_reflection_definition(
    definition: &MemberRef,
    env: &Environment<'_>,
) -> Result<(), String> {
    check_member(definition, env)?;
    if function_info(definition, env).is_none() {
        return Err(format!(
            "Boolean reflection names a forward or missing definition `{}`",
            member_key(definition)
        ));
    }
    Ok(())
}

fn check_boolean_reflection(
    reflection: &SemanticReflection,
    locals: &BTreeMap<String, SemanticType>,
    env: &Environment<'_>,
) -> Result<(), String> {
    for reserved in [
        "llAndBridge",
        "llBeqBridge",
        "llBeqRefl",
        "llIH",
        "llRest",
        "llValue",
    ] {
        if locals.contains_key(reserved) {
            return Err(format!(
                "Boolean reflection reserves internal binder `{reserved}`"
            ));
        }
    }
    match reflection {
        SemanticReflection::List {
            parameter,
            values,
            boolean_definition,
            proposition_definition,
            ..
        } => {
            if locals.get(parameter) != Some(&SemanticType::Nat) {
                return Err(format!(
                    "Boolean list reflection parameter `{parameter}` is not an in-scope Nat"
                ));
            }
            if locals.get(values)
                != Some(&SemanticType::List {
                    element: Box::new(SemanticType::Nat),
                })
            {
                return Err(format!(
                    "Boolean list reflection value `{values}` is not an in-scope List Nat"
                ));
            }
            check_reflection_definition(boolean_definition, env)?;
            check_reflection_definition(proposition_definition, env)
        }
        SemanticReflection::Record {
            record,
            boolean_definition,
            proposition_definition,
            fields,
        } => {
            let SemanticType::Named { member, .. } = locals
                .get(record)
                .ok_or_else(|| format!("Boolean record reflection local `{record}` is absent"))?
            else {
                return Err(format!(
                    "Boolean record reflection local `{record}` is not a document structure"
                ));
            };
            let info = type_info(member, env).ok_or_else(|| {
                format!(
                    "Boolean record reflection type `{}` is absent",
                    member_key(member)
                )
            })?;
            if info.class
                || info.fields.is_empty()
                || info.fields.len() != fields.len()
                || info
                    .field_types
                    .iter()
                    .any(|field| field != &SemanticType::Nat)
                || info
                    .fields
                    .iter()
                    .zip(fields)
                    .any(|(expected, field)| expected != &field.field)
            {
                return Err("Boolean record reflection requires every ordered Nat field".to_owned());
            }
            for field in fields {
                check_name(&field.field, "reflected record field")?;
                if field.expected != "0"
                    && (!field.expected.bytes().all(|byte| byte.is_ascii_digit())
                        || field.expected.starts_with('0'))
                {
                    return Err(format!(
                        "Boolean record reflection has noncanonical Nat literal `{}`",
                        field.expected
                    ));
                }
            }
            check_reflection_definition(boolean_definition, env)?;
            check_reflection_definition(proposition_definition, env)
        }
    }
}

fn check_elimination_proof(
    scrutinee: &str,
    branches: &[SemanticProofBranch],
    induction: bool,
    locals: &BTreeMap<String, SemanticType>,
    env: &Environment<'_>,
) -> Result<(), String> {
    let ty = locals
        .get(scrutinee)
        .ok_or_else(|| format!("proof scrutinee `{scrutinee}` is absent"))?;
    let expected: BTreeMap<String, Vec<SemanticType>> = match ty {
        SemanticType::List { element } => BTreeMap::from([
            (
                "cons".to_owned(),
                if induction {
                    vec![element.as_ref().clone(), ty.clone(), SemanticType::Prop]
                } else {
                    vec![element.as_ref().clone(), ty.clone()]
                },
            ),
            ("nil".to_owned(), Vec::new()),
        ]),
        SemanticType::Nat => BTreeMap::from([
            (
                "succ".to_owned(),
                if induction {
                    vec![SemanticType::Nat, SemanticType::Prop]
                } else {
                    vec![SemanticType::Nat]
                },
            ),
            ("zero".to_owned(), Vec::new()),
        ]),
        SemanticType::Named { member, arguments } => {
            let info = type_info(member, env).ok_or_else(|| {
                format!("proof scrutinee `{scrutinee}` has an unavailable inductive type")
            })?;
            if info.constructors.is_empty() || !info.fields.is_empty() {
                return Err(format!(
                    "proof scrutinee `{scrutinee}` does not have an inductive type"
                ));
            }
            let substitutions = substitutions(info, arguments);
            info.constructor_types
                .iter()
                .map(|(name, fields)| {
                    (
                        name.rsplit('.').next().unwrap_or(name).to_owned(),
                        fields
                            .iter()
                            .map(|field| substitute_type(field, &substitutions))
                            .collect(),
                    )
                })
                .collect()
        }
        _ => {
            return Err(format!(
                "proof scrutinee `{scrutinee}` is not Nat, List, or a document inductive"
            ));
        }
    };
    let mut observed = BTreeMap::new();
    for branch in branches {
        check_name(&branch.constructor, "proof constructor")?;
        if observed
            .insert(branch.constructor.clone(), branch.binders.len())
            .is_some()
        {
            return Err(format!("duplicate proof branch `{}`", branch.constructor));
        }
        let expected_binders = expected.get(&branch.constructor).ok_or_else(|| {
            format!(
                "proof branch `{}` is not a constructor of `{scrutinee}`",
                branch.constructor
            )
        })?;
        if branch.binders.len() != expected_binders.len() {
            return Err(format!(
                "proof branch `{}` expects {} binder(s), received {}",
                branch.constructor,
                expected_binders.len(),
                branch.binders.len()
            ));
        }
        let mut nested = locals.clone();
        for (binder, binder_type) in branch.binders.iter().zip(expected_binders) {
            check_name(binder, "proof binder")?;
            if nested.insert(binder.clone(), binder_type.clone()).is_some() {
                return Err(format!("shadowed proof binder `{binder}`"));
            }
        }
        check_proof(&branch.proof, &nested, env)?;
    }
    if observed.keys().collect::<Vec<_>>() != expected.keys().collect::<Vec<_>>() {
        return Err(format!(
            "proof branches are not exhaustive: expected {:?}, observed {:?}",
            expected.keys().collect::<Vec<_>>(),
            observed.keys().collect::<Vec<_>>()
        ));
    }
    Ok(())
}

impl SemanticModule {
    /// Decode canonical JSON and enforce all conservative semantic checks.
    pub fn parse(
        text: &str,
        imports: &[String],
        imported_modules: &BTreeMap<String, &Self>,
    ) -> Result<Self, String> {
        let module: Self = serde_json::from_str(text)
            .map_err(|error| format!("invalid semantic-module JSON: {error}"))?;
        let canonical =
            crate::artifact::canonical_json::Json::parse(text.as_bytes())?.to_canonical_string();
        if canonical != text {
            return Err("semantic-module JSON is not canonical".to_owned());
        }
        module.validate(imports, imported_modules)?;
        Ok(module)
    }

    fn validate(
        &self,
        imports: &[String],
        imported_modules: &BTreeMap<String, &Self>,
    ) -> Result<(), String> {
        if self.spec != "lexlean/semantic-module/1" {
            return Err(format!(
                "unsupported semantic-module schema `{}`",
                self.spec
            ));
        }
        if self.declarations.is_empty() {
            return Err("a semantic module contains at least one declaration".to_owned());
        }
        let mut env = Environment {
            imports,
            ..Environment::default()
        };
        for import in imports {
            let Some(module) = imported_modules.get(import) else {
                continue;
            };
            for declaration in &module.declarations {
                let key = format!("{import}::{}", declaration.name());
                match declaration {
                    SemanticDeclaration::Structure {
                        type_parameters,
                        fields,
                        ..
                    }
                    | SemanticDeclaration::Class {
                        type_parameters,
                        fields,
                        ..
                    } => {
                        let field_types: Vec<_> = fields
                            .iter()
                            .map(|field| qualify_type(&field.r#type, import))
                            .collect();
                        env.types.insert(
                            key,
                            TypeInfo {
                                parameters: type_parameters.len(),
                                fields: fields.iter().map(|field| field.name.clone()).collect(),
                                constructors: BTreeMap::from([(
                                    format!("{}.mk", declaration.name()),
                                    fields.len(),
                                )]),
                                type_parameters: type_parameters.clone(),
                                field_types: field_types.clone(),
                                constructor_types: BTreeMap::from([(
                                    format!("{}.mk", declaration.name()),
                                    field_types,
                                )]),
                                class: matches!(declaration, SemanticDeclaration::Class { .. }),
                            },
                        );
                    }
                    SemanticDeclaration::Inductive {
                        type_parameters,
                        constructors,
                        ..
                    } => {
                        env.types.insert(
                            key,
                            TypeInfo {
                                parameters: type_parameters.len(),
                                fields: Vec::new(),
                                constructors: constructors
                                    .iter()
                                    .map(|constructor| {
                                        (
                                            format!("{}.{}", declaration.name(), constructor.name),
                                            constructor.fields.len(),
                                        )
                                    })
                                    .collect(),
                                type_parameters: type_parameters.clone(),
                                field_types: Vec::new(),
                                constructor_types: constructors
                                    .iter()
                                    .map(|constructor| {
                                        (
                                            format!("{}.{}", declaration.name(), constructor.name),
                                            constructor
                                                .fields
                                                .iter()
                                                .map(|field| qualify_type(field, import))
                                                .collect(),
                                        )
                                    })
                                    .collect(),
                                class: false,
                            },
                        );
                    }
                    SemanticDeclaration::Definition {
                        parameters, result, ..
                    } => {
                        env.functions.insert(
                            key,
                            FunctionInfo {
                                parameters: parameters
                                    .iter()
                                    .map(|parameter| qualify_type(&parameter.r#type, import))
                                    .collect(),
                                result: qualify_type(result, import),
                            },
                        );
                    }
                    SemanticDeclaration::Instance {
                        name,
                        class,
                        arguments,
                        ..
                    } => {
                        let class = MemberRef {
                            module: class.module.clone().or_else(|| Some(import.clone())),
                            name: class.name.clone(),
                        };
                        let arguments = arguments
                            .iter()
                            .map(|argument| qualify_type(argument, import))
                            .collect::<Vec<_>>();
                        let key = format!("{}:{arguments:?}", member_key(&class));
                        let instance = MemberRef {
                            module: Some(import.clone()),
                            name: name.clone(),
                        };
                        if env.instances.insert(key.clone(), instance).is_some() {
                            return Err(format!(
                                "ambiguous imported instances for requirement `{key}`"
                            ));
                        }
                    }
                    SemanticDeclaration::Theorem { parameters, .. } => {
                        env.proof_rules.insert(
                            key,
                            parameters
                                .iter()
                                .map(|parameter| qualify_type(&parameter.r#type, import))
                                .collect(),
                        );
                    }
                }
            }
        }
        let mut generated_names = BTreeSet::new();
        for declaration in &self.declarations {
            let name = declaration.name();
            check_name(name, "declaration")?;
            if !generated_names.insert(name.to_owned()) {
                return Err(format!("duplicate generated name `{name}`"));
            }
            match declaration {
                SemanticDeclaration::Structure {
                    type_parameters,
                    parameters,
                    fields,
                    ..
                }
                | SemanticDeclaration::Class {
                    type_parameters,
                    parameters,
                    fields,
                    ..
                } => {
                    if !parameters.is_empty() {
                        return Err(format!(
                            "`{name}` value parameters are not part of a finite data declaration"
                        ));
                    }
                    let type_parameter_names = type_parameters.clone();
                    let type_parameters = type_parameter_set(type_parameters)?;
                    let _ = check_parameters(parameters, &env, &type_parameters)?;
                    if fields.is_empty() {
                        return Err(format!("`{name}` has no fields"));
                    }
                    let mut field_names = Vec::new();
                    for field in fields {
                        check_name(&field.name, "field")?;
                        check_type(&field.r#type, &env)?;
                        check_type_parameters(&field.r#type, &type_parameters)?;
                        if field_names.contains(&field.name) {
                            return Err(format!("duplicate field `{}.{}`", name, field.name));
                        }
                        field_names.push(field.name.clone());
                        let generated = format!("{name}.{}", field.name);
                        if !generated_names.insert(generated.clone()) {
                            return Err(format!("duplicate generated name `{generated}`"));
                        }
                    }
                    let constructor = format!("{name}.mk");
                    if !generated_names.insert(constructor.clone()) {
                        return Err(format!("duplicate generated name `{constructor}`"));
                    }
                    env.types.insert(
                        name.to_owned(),
                        TypeInfo {
                            parameters: type_parameters.len(),
                            fields: field_names,
                            constructors: BTreeMap::from([(format!("{name}.mk"), fields.len())]),
                            type_parameters: type_parameter_names,
                            field_types: fields.iter().map(|field| field.r#type.clone()).collect(),
                            constructor_types: BTreeMap::from([(
                                format!("{name}.mk"),
                                fields.iter().map(|field| field.r#type.clone()).collect(),
                            )]),
                            class: matches!(declaration, SemanticDeclaration::Class { .. }),
                        },
                    );
                }
                SemanticDeclaration::Inductive {
                    type_parameters,
                    parameters,
                    constructors,
                    ..
                } => {
                    if !parameters.is_empty() {
                        return Err(format!(
                            "inductive `{name}` value parameters are not part of a finite data declaration"
                        ));
                    }
                    let type_parameter_names = type_parameters.clone();
                    let type_parameters = type_parameter_set(type_parameters)?;
                    let _ = check_parameters(parameters, &env, &type_parameters)?;
                    if constructors.is_empty() {
                        return Err(format!("inductive `{name}` has no constructors"));
                    }
                    let mut rows = BTreeMap::new();
                    let mut constructor_types = BTreeMap::new();
                    for constructor in constructors {
                        check_name(&constructor.name, "constructor")?;
                        let full = format!("{name}.{}", constructor.name);
                        if !generated_names.insert(full.clone()) {
                            return Err(format!("duplicate generated name `{full}`"));
                        }
                        for field in &constructor.fields {
                            check_type(field, &env)?;
                            check_type_parameters(field, &type_parameters)?;
                            if matches!(field, SemanticType::Named { member, .. } if member.module.is_none() && member.name == *name)
                            {
                                return Err(format!(
                                    "recursive inductive payload in `{full}` is not permitted"
                                ));
                            }
                        }
                        rows.insert(full.clone(), constructor.fields.len());
                        constructor_types.insert(full, constructor.fields.clone());
                    }
                    env.types.insert(
                        name.to_owned(),
                        TypeInfo {
                            parameters: type_parameters.len(),
                            fields: Vec::new(),
                            constructors: rows,
                            type_parameters: type_parameter_names,
                            field_types: Vec::new(),
                            constructor_types,
                            class: false,
                        },
                    );
                }
                SemanticDeclaration::Instance {
                    class,
                    arguments,
                    priority,
                    fields,
                    ..
                } => {
                    check_member(class, &env)?;
                    if *priority != 1000 {
                        return Err(format!("instance `{name}` priority must be exactly 1000"));
                    }
                    for argument in arguments {
                        check_type(argument, &env)?;
                    }
                    let info = type_info(class, &env)
                        .filter(|info| info.class)
                        .cloned()
                        .ok_or_else(|| {
                            format!("instance `{name}` targets a missing or non-class type")
                        })?;
                    if info.parameters != arguments.len() {
                        return Err(format!("instance `{name}` has the wrong class arity"));
                    }
                    let key = format!("{}:{arguments:?}", member_key(class));
                    if env.instances.contains_key(&key) {
                        return Err(format!("ambiguous duplicate instance for `{}`", class.name));
                    }
                    check_assignments(
                        fields,
                        &info.fields,
                        &BTreeSet::new(),
                        &env,
                        None,
                        &BTreeSet::new(),
                    )?;
                    let map = substitutions(&info, arguments);
                    for (assignment, expected) in fields.iter().zip(&info.field_types) {
                        require_type(
                            infer_term(&assignment.value, &BTreeMap::new(), &env)?,
                            &substitute_type(expected, &map),
                            &format!("instance field `{}.{}`", name, assignment.field),
                        )?;
                    }
                    env.instances.insert(
                        key,
                        MemberRef {
                            module: None,
                            name: name.to_owned(),
                        },
                    );
                }
                SemanticDeclaration::Definition {
                    parameters,
                    result,
                    recursive_argument,
                    body,
                    ..
                } => {
                    let locals = check_parameters(parameters, &env, &BTreeSet::new())?;
                    check_type(result, &env)?;
                    let recursion = if let Some(argument) = recursive_argument {
                        let index = parameters
                            .iter()
                            .position(|parameter| &parameter.name == argument)
                            .ok_or_else(|| format!("definition `{name}` names a missing decreasing argument `{argument}`"))?;
                        if !is_structural_domain(&parameters[index].r#type, &env) {
                            return Err(format!(
                                "definition `{name}` decreasing argument `{argument}` is not Nat, List, or a document inductive"
                            ));
                        }
                        if !matches!(
                            body,
                            SemanticTerm::Match { scrutinee, .. }
                                if matches!(scrutinee.as_ref(), SemanticTerm::Var { name } if name == argument)
                        ) {
                            return Err(format!(
                                "definition `{name}` is recursive but its body is not a top-level match on `{argument}`"
                            ));
                        }
                        Some((name, index, argument.as_str()))
                    } else {
                        None
                    };
                    check_term(body, &locals, &env, recursion, &BTreeSet::new())?;
                    env.functions.insert(
                        name.to_owned(),
                        FunctionInfo {
                            parameters: parameters
                                .iter()
                                .map(|parameter| parameter.r#type.clone())
                                .collect(),
                            result: result.clone(),
                        },
                    );
                    require_type(
                        infer_term(body, &typed_locals(parameters), &env)?,
                        result,
                        &format!("definition `{name}` body"),
                    )?;
                }
                SemanticDeclaration::Theorem {
                    parameters,
                    statement,
                    proof,
                    axioms,
                    ..
                } => {
                    if axioms.windows(2).any(|pair| pair[0] >= pair[1])
                        || axioms.iter().any(|axiom| !legal_name(axiom))
                    {
                        return Err(format!(
                            "theorem `{name}` axiom policy is not sorted, unique, and qualified"
                        ));
                    }
                    let locals = check_parameters(parameters, &env, &BTreeSet::new())?;
                    check_term(statement, &locals, &env, None, &BTreeSet::new())?;
                    require_type(
                        infer_term(statement, &typed_locals(parameters), &env)?,
                        &SemanticType::Prop,
                        &format!("theorem `{name}` statement"),
                    )?;
                    check_proof(proof, &typed_locals(parameters), &env)?;
                    env.proof_rules.insert(
                        name.to_owned(),
                        parameters
                            .iter()
                            .map(|parameter| parameter.r#type.clone())
                            .collect(),
                    );
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::SemanticModule;

    const EMPTY_POLICY: &str = r#"{"declarations":[{"kind":"theorem","name":"zero_refl","parameters":[],"proof":{"kind":"reflexivity"},"statement":{"kind":"eq","left":{"kind":"nat","value":"0"},"right":{"kind":"nat","value":"0"}}}],"spec":"lexlean/semantic-module/1"}"#;

    fn theorem_with_axioms(axioms: &str) -> String {
        format!(
            r#"{{"declarations":[{{"axioms":{axioms},"kind":"theorem","name":"zero_refl","parameters":[],"proof":{{"kind":"reflexivity"}},"statement":{{"kind":"eq","left":{{"kind":"nat","value":"0"}},"right":{{"kind":"nat","value":"0"}}}}}}],"spec":"lexlean/semantic-module/1"}}"#
        )
    }

    #[test]
    fn semantic_theorem_policy_defaults_to_exact_empty() {
        let module = SemanticModule::parse(EMPTY_POLICY, &[], &BTreeMap::new())
            .expect("omitted policy is exact empty");
        let declaration = module.declarations.first().expect("one theorem");
        assert_eq!(declaration.axiom_policy_kind(), "none");
        assert!(declaration.axioms().is_empty());
    }

    #[test]
    fn semantic_theorem_policy_round_trips_a_nonempty_exact_set() {
        let source = theorem_with_axioms(r#"["Classical.choice","propext"]"#);
        let module = SemanticModule::parse(&source, &[], &BTreeMap::new())
            .expect("sorted exact policy is valid");
        let declaration = module.declarations.first().expect("one theorem");
        assert_eq!(declaration.axiom_policy_kind(), "exact");
        assert_eq!(declaration.axioms(), ["Classical.choice", "propext"]);
        let encoded = serde_json::to_value(declaration).expect("serialize theorem");
        assert_eq!(
            encoded.get("axioms").expect("serialized policy"),
            &serde_json::json!(["Classical.choice", "propext"])
        );
    }

    #[test]
    fn semantic_theorem_policy_rejects_unsorted_duplicate_or_invalid_names() {
        for axioms in [
            r#"["propext","Classical.choice"]"#,
            r#"["propext","propext"]"#,
            r#"["bad-name"]"#,
        ] {
            let error = SemanticModule::parse(&theorem_with_axioms(axioms), &[], &BTreeMap::new())
                .expect_err("invalid exact policy must fail");
            assert!(
                error.contains("not sorted, unique, and qualified"),
                "{error}"
            );
        }
    }
}
