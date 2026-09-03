//! Deterministic Lean and LaTeX lowering for language-1.1 semantic modules.

use crate::artifact::source_map::MapRole;
use crate::backend::{EmitSource, Emitter};
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{
    MemberRef, SemanticAssignment, SemanticBranch, SemanticDeclaration, SemanticModule,
    SemanticParameter, SemanticPrimitive, SemanticProof, SemanticProofBranch, SemanticReflection,
    SemanticReflectionComparison, SemanticReflectionField, SemanticTerm, SemanticType,
};
use crate::link::CheckedModule;
use crate::source::coverage::Origin;

struct Render<'a> {
    prefix: &'a str,
}

fn term_uses(term: &SemanticTerm, local: &str) -> bool {
    let pair = |left: &SemanticTerm, right: &SemanticTerm| {
        term_uses(left, local) || term_uses(right, local)
    };
    match term {
        SemanticTerm::Var { name } => name == local,
        SemanticTerm::Nat { .. }
        | SemanticTerm::Integer { .. }
        | SemanticTerm::String { .. }
        | SemanticTerm::Bytes { .. }
        | SemanticTerm::Bool { .. }
        | SemanticTerm::Unit
        | SemanticTerm::Nil { .. }
        | SemanticTerm::InstanceValue { .. } => false,
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
            term_uses(value, local)
        }
        SemanticTerm::Record { fields, .. } => fields
            .iter()
            .any(|assignment| term_uses(&assignment.value, local)),
        SemanticTerm::Constructor { arguments, .. }
        | SemanticTerm::Call { arguments, .. }
        | SemanticTerm::Primitive { arguments, .. } => {
            arguments.iter().any(|argument| term_uses(argument, local))
        }
        SemanticTerm::If {
            condition,
            then_value,
            else_value,
        } => {
            term_uses(condition, local)
                || term_uses(then_value, local)
                || term_uses(else_value, local)
        }
        SemanticTerm::Match {
            scrutinee,
            branches,
        } => {
            term_uses(scrutinee, local)
                || branches.iter().any(|branch| term_uses(&branch.body, local))
        }
        SemanticTerm::Forall { binder, body } => binder.name != local && term_uses(body, local),
    }
}

fn reflected_projection(record: &str, field: &SemanticReflectionField) -> String {
    format!("({record}).{}", field.field)
}

fn reflected_bool(record: &str, fields: &[SemanticReflectionField]) -> String {
    let field = &fields[0];
    let comparison = format!(
        "Nat.beq ({}) ({})",
        reflected_projection(record, field),
        field.expected
    );
    if fields.len() == 1 {
        comparison
    } else {
        format!("({comparison} && {})", reflected_bool(record, &fields[1..]))
    }
}

fn reflected_prop(record: &str, fields: &[SemanticReflectionField]) -> String {
    let field = &fields[0];
    let comparison = format!(
        "({} = {})",
        reflected_projection(record, field),
        field.expected
    );
    if fields.len() == 1 {
        comparison
    } else {
        format!(
            "({comparison} /\\ {})",
            reflected_prop(record, &fields[1..])
        )
    }
}

fn reflected_iff(fields: &[SemanticReflectionField]) -> String {
    if fields.len() == 1 {
        "llBeqBridge _ _".to_owned()
    } else {
        format!(
            "Iff.trans (llAndBridge _ _) (and_congr (llBeqBridge _ _) ({}))",
            reflected_iff(&fields[1..])
        )
    }
}

impl Render<'_> {
    fn member(&self, member: &MemberRef) -> String {
        if member.module.is_none() {
            match member.name.as_str() {
                "Result.error" => return "Except.error".to_owned(),
                "Result.ok" => return "Except.ok".to_owned(),
                _ => {}
            }
        }
        member.module.as_ref().map_or_else(
            || member.name.clone(),
            |module| format!("{}.{}.{}", self.prefix, module, member.name),
        )
    }

    fn ty(&self, ty: &SemanticType) -> String {
        match ty {
            SemanticType::Type => "Type".to_owned(),
            SemanticType::Parameter { name } => name.clone(),
            SemanticType::Nat => "Nat".to_owned(),
            SemanticType::Bool => "Bool".to_owned(),
            SemanticType::Prop => "Prop".to_owned(),
            SemanticType::Unit => "Unit".to_owned(),
            SemanticType::Int => "Int".to_owned(),
            SemanticType::Int8 => "Int8".to_owned(),
            SemanticType::Int16 => "Int16".to_owned(),
            SemanticType::Int32 => "Int32".to_owned(),
            SemanticType::Int64 => "Int64".to_owned(),
            SemanticType::UInt8 => "UInt8".to_owned(),
            SemanticType::UInt16 => "UInt16".to_owned(),
            SemanticType::UInt32 => "UInt32".to_owned(),
            SemanticType::UInt64 => "UInt64".to_owned(),
            SemanticType::String => "String".to_owned(),
            SemanticType::Bytes => "ByteArray".to_owned(),
            SemanticType::Ordering => "Ordering".to_owned(),
            SemanticType::Option { value } => format!("Option ({})", self.ty(value)),
            SemanticType::Result { ok, error } => {
                format!("Except ({}) ({})", self.ty(error), self.ty(ok))
            }
            SemanticType::List { element } => format!("List ({})", self.ty(element)),
            SemanticType::Named { member, arguments } => {
                let mut out = self.member(member);
                for argument in arguments {
                    out.push_str(" (");
                    out.push_str(&self.ty(argument));
                    out.push(')');
                }
                out
            }
        }
    }

    fn parameters(&self, parameters: &[SemanticParameter]) -> String {
        parameters
            .iter()
            .map(|parameter| format!(" ({} : {})", parameter.name, self.ty(&parameter.r#type)))
            .collect()
    }

    fn recursive_equations(
        &self,
        name: &str,
        parameters: &[SemanticParameter],
        result: &SemanticType,
        recursive_argument: &str,
        body: &SemanticTerm,
    ) -> Option<String> {
        let SemanticTerm::Match {
            scrutinee,
            branches,
        } = body
        else {
            return None;
        };
        if !matches!(scrutinee.as_ref(), SemanticTerm::Var { name } if name == recursive_argument) {
            return None;
        }
        let mut text = format!("@[expose] public def {name} :");
        for parameter in parameters {
            text.push_str(&format!(
                " ({} : {}) ->",
                parameter.name,
                self.ty(&parameter.r#type)
            ));
        }
        text.push_str(&format!(" {}\n", self.ty(result)));
        for branch in branches {
            let patterns = parameters
                .iter()
                .map(|parameter| {
                    if parameter.name == recursive_argument {
                        let binders = if branch.binders.is_empty() {
                            String::new()
                        } else {
                            format!(
                                " {}",
                                branch
                                    .binders
                                    .iter()
                                    .map(|binder| {
                                        if term_uses(&branch.body, binder) {
                                            binder.as_str()
                                        } else {
                                            "_"
                                        }
                                    })
                                    .collect::<Vec<_>>()
                                    .join(" ")
                            )
                        };
                        format!("{}{}", self.member(&branch.constructor), binders)
                    } else if term_uses(&branch.body, &parameter.name) {
                        parameter.name.clone()
                    } else {
                        format!("_{}", parameter.name)
                    }
                })
                .collect::<Vec<_>>()
                .join(", ");
            text.push_str(&format!("  | {patterns} => {}\n", self.term(&branch.body)));
        }
        Some(text)
    }

    fn type_parameters(&self, parameters: &[String]) -> String {
        parameters
            .iter()
            .map(|parameter| format!(" ({parameter} : Type)"))
            .collect()
    }

    fn assignments(&self, assignments: &[SemanticAssignment]) -> String {
        assignments
            .iter()
            .map(|row| format!("{} := {}", row.field, self.term(&row.value)))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn branch(&self, branch: &SemanticBranch) -> String {
        let binders = if branch.binders.is_empty() {
            String::new()
        } else {
            format!(
                " {}",
                branch
                    .binders
                    .iter()
                    .map(|binder| {
                        if term_uses(&branch.body, binder) {
                            binder.as_str()
                        } else {
                            "_"
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        };
        format!(
            "| {}{} => {}",
            self.member(&branch.constructor),
            binders,
            self.term(&branch.body)
        )
    }

    fn primitive(
        &self,
        operation: SemanticPrimitive,
        arguments: &[SemanticTerm],
        result: &SemanticType,
    ) -> String {
        let int64_specialization = match operation {
            SemanticPrimitive::CheckedAdd => Some("checkedAddInt64"),
            SemanticPrimitive::CheckedSubtract => Some("checkedSubtractInt64"),
            SemanticPrimitive::CheckedMultiply => Some("checkedMultiplyInt64"),
            SemanticPrimitive::CheckedNegate => Some("checkedNegateInt64"),
            SemanticPrimitive::CheckedQuotient => Some("checkedQuotientInt64"),
            _ => None,
        };
        if matches!(result, SemanticType::Option { value } if **value == SemanticType::Int64) {
            if let Some(operation) = int64_specialization {
                let mut out = format!("(LexLeanRuntime.{operation}");
                for argument in arguments {
                    out.push_str(" (");
                    out.push_str(&self.term(argument));
                    out.push(')');
                }
                out.push_str(" : Option (Int64))");
                return out;
            }
        }
        let operation = match operation {
            SemanticPrimitive::Subtract => "subtract",
            SemanticPrimitive::Multiply => "multiply",
            SemanticPrimitive::Quotient => "quotient",
            SemanticPrimitive::Remainder => "remainder",
            SemanticPrimitive::Negate => "negate",
            SemanticPrimitive::CheckedConvert => "checkedConvert",
            SemanticPrimitive::CheckedAdd => "checkedAdd",
            SemanticPrimitive::CheckedSubtract => "checkedSubtract",
            SemanticPrimitive::CheckedMultiply => "checkedMultiply",
            SemanticPrimitive::CheckedNegate => "checkedNegate",
            SemanticPrimitive::CheckedQuotient => "checkedQuotient",
            SemanticPrimitive::BitAnd => "bitAnd",
            SemanticPrimitive::BitOr => "bitOr",
            SemanticPrimitive::BitXor => "bitXor",
            SemanticPrimitive::BitNot => "bitNot",
            SemanticPrimitive::ShiftLeft => "shiftLeft",
            SemanticPrimitive::ShiftRight => "shiftRight",
            SemanticPrimitive::Append => "append",
            SemanticPrimitive::Length => "length",
            SemanticPrimitive::Index => "index",
            SemanticPrimitive::Slice => "slice",
            SemanticPrimitive::Utf8Encode => "utf8Encode",
            SemanticPrimitive::Utf8Decode => "utf8Decode",
            SemanticPrimitive::CompareBytes => "compareBytes",
            SemanticPrimitive::Equal => "equal",
            SemanticPrimitive::SplitExact => "splitExact",
            SemanticPrimitive::Join => "join",
            SemanticPrimitive::ParseDecimal => "parseDecimal",
            SemanticPrimitive::FormatDecimal => "formatDecimal",
        };
        let mut out = format!("(LexLeanRuntime.{operation}");
        for argument in arguments {
            out.push_str(" (");
            out.push_str(&self.term(argument));
            out.push(')');
        }
        out.push_str(" : ");
        out.push_str(&self.ty(result));
        out.push(')');
        out
    }

    #[allow(clippy::too_many_lines)]
    fn term(&self, term: &SemanticTerm) -> String {
        let binary = |operator: &str, left: &SemanticTerm, right: &SemanticTerm| {
            format!("({} {operator} {})", self.term(left), self.term(right))
        };
        match term {
            SemanticTerm::Var { name } => name.clone(),
            SemanticTerm::Nat { value } => value.clone(),
            SemanticTerm::Integer {
                representation,
                value,
            } => format!("({value} : {representation:?})"),
            SemanticTerm::String { value } => format!("{value:?}"),
            SemanticTerm::Bytes { hex } => {
                let values = hex
                    .as_bytes()
                    .chunks_exact(2)
                    .map(|pair| {
                        let pair = core::str::from_utf8(pair).expect("validated byte literal");
                        u8::from_str_radix(pair, 16).expect("validated byte literal")
                    })
                    .map(|value| value.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("ByteArray.mk #[{values}]")
            }
            SemanticTerm::Primitive {
                operation,
                arguments,
                result,
            } => self.primitive(*operation, arguments, result),
            SemanticTerm::Bool { value } => value.to_string(),
            SemanticTerm::Unit => "()".to_owned(),
            SemanticTerm::Nil { element } => format!("([] : List ({}))", self.ty(element)),
            SemanticTerm::Cons { head, tail } => {
                format!("({} :: {})", self.term(head), self.term(tail))
            }
            SemanticTerm::Record {
                r#type,
                type_arguments,
                fields,
            } => {
                let annotation = SemanticType::Named {
                    member: r#type.clone(),
                    arguments: type_arguments.clone(),
                };
                format!(
                    "({{ {} }} : {})",
                    self.assignments(fields),
                    self.ty(&annotation)
                )
            }
            SemanticTerm::Constructor {
                constructor,
                type_arguments: _,
                arguments,
            } => {
                let mut out = self.member(constructor);
                for argument in arguments {
                    out.push_str(" (");
                    out.push_str(&self.term(argument));
                    out.push(')');
                }
                out
            }
            SemanticTerm::InstanceValue { resolved, .. } => self.member(resolved),
            SemanticTerm::Project { value, field } => {
                format!("({}).{field}", self.term(value))
            }
            SemanticTerm::Call {
                function,
                arguments,
            } => {
                let mut out = self.member(function);
                for argument in arguments {
                    out.push_str(" (");
                    out.push_str(&self.term(argument));
                    out.push(')');
                }
                out
            }
            SemanticTerm::If {
                condition,
                then_value,
                else_value,
            } => format!(
                "(if {} then {} else {})",
                self.term(condition),
                self.term(then_value),
                self.term(else_value)
            ),
            SemanticTerm::Match {
                scrutinee,
                branches,
            } => format!(
                "(match {} with {})",
                self.term(scrutinee),
                branches
                    .iter()
                    .map(|branch| self.branch(branch))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            SemanticTerm::Eq { left, right } => binary("=", left, right),
            SemanticTerm::Le { left, right } => binary("<=", left, right),
            SemanticTerm::Lt { left, right } => binary("<", left, right),
            SemanticTerm::Add { left, right } => binary("+", left, right),
            SemanticTerm::Beq { left, right } => {
                format!("(Nat.beq ({}) ({}))", self.term(left), self.term(right))
            }
            SemanticTerm::Ble { left, right } => {
                format!("(Nat.ble ({}) ({}))", self.term(left), self.term(right))
            }
            SemanticTerm::Blt { left, right } => {
                format!("(Nat.blt ({}) ({}))", self.term(left), self.term(right))
            }
            SemanticTerm::And { left, right } => binary("&&", left, right),
            SemanticTerm::PropAnd { left, right } => binary("/\\", left, right),
            SemanticTerm::Or { left, right } => binary("||", left, right),
            SemanticTerm::Not { value } => format!("(!{})", self.term(value)),
            SemanticTerm::Implies {
                premise,
                conclusion,
            } => binary("->", premise, conclusion),
            SemanticTerm::Iff { left, right } => binary("<->", left, right),
            SemanticTerm::Forall { binder, body } => format!(
                "(forall ({} : {}), {})",
                binder.name,
                self.ty(&binder.r#type),
                self.term(body)
            ),
        }
    }

    fn proof_branch(&self, branch: &SemanticProofBranch, indent: usize) -> String {
        let binders = if branch.binders.is_empty() {
            String::new()
        } else {
            format!(" {}", branch.binders.join(" "))
        };
        format!(
            "{}| {}{} =>\n{}",
            "  ".repeat(indent),
            branch.constructor,
            binders,
            self.proof(&branch.proof, indent + 1)
        )
    }

    fn proof(&self, proof: &SemanticProof, indent: usize) -> String {
        let pad = "  ".repeat(indent);
        match proof {
            SemanticProof::Reflexivity => format!("{pad}rfl\n"),
            SemanticProof::Decide => format!("{pad}decide\n"),
            SemanticProof::Simplify { definitions } => format!(
                "{pad}simp only [{}]\n",
                definitions
                    .iter()
                    .map(|member| self.member(member))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            SemanticProof::Constructor { branches } => {
                let mut out = format!("{pad}constructor\n");
                for branch in branches {
                    out.push_str(&format!("{pad}·\n"));
                    out.push_str(&self.proof(branch, indent + 1));
                }
                out
            }
            SemanticProof::Cases {
                scrutinee,
                branches,
            } => {
                let mut out = format!("{pad}cases {scrutinee} with\n");
                for branch in branches {
                    out.push_str(&self.proof_branch(branch, indent));
                }
                out
            }
            SemanticProof::Induction {
                scrutinee,
                generalizing,
                branches,
            } => {
                let generalizing = if generalizing.is_empty() {
                    String::new()
                } else {
                    format!(" generalizing {}", generalizing.join(" "))
                };
                let mut out = format!("{pad}induction {scrutinee}{generalizing} with\n");
                for branch in branches {
                    out.push_str(&self.proof_branch(branch, indent));
                }
                out
            }
            SemanticProof::Congruence => format!("{pad}congr 1\n"),
            SemanticProof::BooleanReflection { reflection } => match reflection {
                SemanticReflection::List {
                    parameter,
                    values,
                    boolean_definition,
                    proposition_definition,
                    comparison,
                } => {
                    let boolean = self.member(boolean_definition);
                    let proposition = self.member(proposition_definition);
                    let mut out = format!(
                        "{pad}have llAndBridge : ∀ left right : Bool, ((left && right) = true) ↔ left = true ∧ right = true := by\n{pad}  intro left right\n{pad}  cases left <;> cases right <;> decide\n"
                    );
                    if matches!(comparison, SemanticReflectionComparison::NatBeq) {
                        out.push_str(&format!(
                            "{pad}have llBeqRefl : ∀ value : Nat, Nat.beq value value = true := by\n{pad}  intro value\n{pad}  induction value with\n{pad}  | zero => rfl\n{pad}  | succ value ih => exact ih\n"
                        ));
                    }
                    out.push_str(&format!(
                        "{pad}induction {values} generalizing {parameter} with\n{pad}| nil => constructor <;> intro _ <;> rfl\n{pad}| cons llValue llRest llIH =>\n{pad}  constructor\n{pad}  · intro h\n{pad}    have hpair := (llAndBridge _ _).mp h\n"
                    ));
                    match comparison {
                        SemanticReflectionComparison::NatBeq => out.push_str(&format!(
                            "{pad}    exact And.intro (Nat.eq_of_beq_eq_true hpair.left) ((llIH ({parameter} + 1)).mp hpair.right)\n{pad}  · intro h\n{pad}    have hleft : Nat.beq {parameter} llValue = true := h.left ▸ llBeqRefl {parameter}\n{pad}    have hright : {boolean} ({parameter} + 1) llRest = true := (llIH ({parameter} + 1)).mpr h.right\n{pad}    exact (llAndBridge _ _).mpr (And.intro hleft hright)\n"
                        )),
                        SemanticReflectionComparison::NatBlt => out.push_str(&format!(
                            "{pad}    exact And.intro (Nat.le_of_ble_eq_true hpair.left) ((llIH {parameter}).mp hpair.right)\n{pad}  · intro h\n{pad}    have hleft : Nat.blt llValue {parameter} = true := Nat.ble_eq_true_of_le h.left\n{pad}    have hright : {boolean} {parameter} llRest = true := (llIH {parameter}).mpr h.right\n{pad}    exact (llAndBridge _ _).mpr (And.intro hleft hright)\n"
                        )),
                    }
                    let _ = proposition;
                    out
                }
                SemanticReflection::Record {
                    record,
                    boolean_definition,
                    proposition_definition,
                    fields,
                } => {
                    let _ = (
                        self.member(boolean_definition),
                        self.member(proposition_definition),
                    );
                    format!(
                        "{pad}have llAndBridge : ∀ left right : Bool, ((left && right) = true) ↔ left = true ∧ right = true := by\n{pad}  intro left right\n{pad}  cases left <;> cases right <;> decide\n{pad}have llBeqRefl : ∀ value : Nat, Nat.beq value value = true := by\n{pad}  intro value\n{pad}  induction value with\n{pad}  | zero => rfl\n{pad}  | succ value ih => exact ih\n{pad}have llBeqBridge : ∀ left right : Nat, Nat.beq left right = true ↔ left = right := by\n{pad}  intro left right\n{pad}  constructor\n{pad}  · exact Nat.eq_of_beq_eq_true\n{pad}  · intro h\n{pad}    cases h\n{pad}    exact llBeqRefl left\n{pad}change (({}) = true) ↔ {}\n{pad}exact {}\n",
                        reflected_bool(record, fields),
                        reflected_prop(record, fields),
                        reflected_iff(fields)
                    )
                }
            },
            SemanticProof::Apply { theorem, arguments } => {
                let arguments = arguments
                    .iter()
                    .map(|argument| format!(" ({})", self.term(argument)))
                    .collect::<String>();
                format!("{pad}exact {}{arguments}\n", self.member(theorem))
            }
        }
    }
}

fn emit(checked: &CheckedModule, text: &str, kind: &str) -> Emitter {
    let mut emitter = Emitter::new();
    let node = emitter.node(kind);
    emitter.piece(
        text,
        kind,
        Origin::Metadata {
            owner: "lexlean.core::semanticdata".to_owned(),
        },
        EmitSource::File(0, checked.normalized.len()),
        MapRole::Declaration,
        node,
    );
    emitter
}

fn portable_runtime() -> &'static str {
    r#"
namespace LexLeanRuntime

public class ToMathInt (α : Type) where
  toInt : α -> Int

public class Fixed (α : Type) extends ToMathInt α where
  fromInt : Int -> α
  minimum : Int
  maximum : Int
  bitAnd : α -> α -> α
  bitOr : α -> α -> α
  bitXor : α -> α -> α
  bitNot : α -> α
  shiftLeft : α -> UInt32 -> Option α
  shiftRight : α -> UInt32 -> Option α

public instance : ToMathInt Int where toInt := fun value => value

public instance : Fixed Int8 where
  toInt := Int8.toInt
  fromInt := Int8.ofInt
  minimum := -128
  maximum := 127
  bitAnd := Int8.land
  bitOr := Int8.lor
  bitXor := Int8.xor
  bitNot := Int8.complement
  shiftLeft := fun value amount => if amount.toNat < 8 then some (Int8.shiftLeft value (Int8.ofNat amount.toNat)) else none
  shiftRight := fun value amount => if amount.toNat < 8 then some (Int8.shiftRight value (Int8.ofNat amount.toNat)) else none

public instance : Fixed Int16 where
  toInt := Int16.toInt
  fromInt := Int16.ofInt
  minimum := -32768
  maximum := 32767
  bitAnd := Int16.land
  bitOr := Int16.lor
  bitXor := Int16.xor
  bitNot := Int16.complement
  shiftLeft := fun value amount => if amount.toNat < 16 then some (Int16.shiftLeft value (Int16.ofNat amount.toNat)) else none
  shiftRight := fun value amount => if amount.toNat < 16 then some (Int16.shiftRight value (Int16.ofNat amount.toNat)) else none

public instance : Fixed Int32 where
  toInt := Int32.toInt
  fromInt := Int32.ofInt
  minimum := -2147483648
  maximum := 2147483647
  bitAnd := Int32.land
  bitOr := Int32.lor
  bitXor := Int32.xor
  bitNot := Int32.complement
  shiftLeft := fun value amount => if amount.toNat < 32 then some (Int32.shiftLeft value (Int32.ofNat amount.toNat)) else none
  shiftRight := fun value amount => if amount.toNat < 32 then some (Int32.shiftRight value (Int32.ofNat amount.toNat)) else none

public instance : Fixed Int64 where
  toInt := Int64.toInt
  fromInt := Int64.ofInt
  minimum := -9223372036854775808
  maximum := 9223372036854775807
  bitAnd := Int64.land
  bitOr := Int64.lor
  bitXor := Int64.xor
  bitNot := Int64.complement
  shiftLeft := fun value amount => if amount.toNat < 64 then some (Int64.shiftLeft value (Int64.ofNat amount.toNat)) else none
  shiftRight := fun value amount => if amount.toNat < 64 then some (Int64.shiftRight value (Int64.ofNat amount.toNat)) else none

public instance : Fixed UInt8 where
  toInt := fun value => Int.ofNat value.toNat
  fromInt := UInt8.ofInt
  minimum := 0
  maximum := 255
  bitAnd := UInt8.land
  bitOr := UInt8.lor
  bitXor := UInt8.xor
  bitNot := UInt8.complement
  shiftLeft := fun value amount => if amount.toNat < 8 then some (UInt8.shiftLeft value (UInt8.ofNat amount.toNat)) else none
  shiftRight := fun value amount => if amount.toNat < 8 then some (UInt8.shiftRight value (UInt8.ofNat amount.toNat)) else none

public instance : Fixed UInt16 where
  toInt := fun value => Int.ofNat value.toNat
  fromInt := UInt16.ofInt
  minimum := 0
  maximum := 65535
  bitAnd := UInt16.land
  bitOr := UInt16.lor
  bitXor := UInt16.xor
  bitNot := UInt16.complement
  shiftLeft := fun value amount => if amount.toNat < 16 then some (UInt16.shiftLeft value (UInt16.ofNat amount.toNat)) else none
  shiftRight := fun value amount => if amount.toNat < 16 then some (UInt16.shiftRight value (UInt16.ofNat amount.toNat)) else none

public instance : Fixed UInt32 where
  toInt := fun value => Int.ofNat value.toNat
  fromInt := UInt32.ofInt
  minimum := 0
  maximum := 4294967295
  bitAnd := UInt32.land
  bitOr := UInt32.lor
  bitXor := UInt32.xor
  bitNot := UInt32.complement
  shiftLeft := fun value amount => if amount.toNat < 32 then some (UInt32.shiftLeft value amount) else none
  shiftRight := fun value amount => if amount.toNat < 32 then some (UInt32.shiftRight value amount) else none

public instance : Fixed UInt64 where
  toInt := fun value => Int.ofNat value.toNat
  fromInt := UInt64.ofInt
  minimum := 0
  maximum := 18446744073709551615
  bitAnd := UInt64.land
  bitOr := UInt64.lor
  bitXor := UInt64.xor
  bitNot := UInt64.complement
  shiftLeft := fun value amount => if amount.toNat < 64 then some (UInt64.shiftLeft value (UInt64.ofNat amount.toNat)) else none
  shiftRight := fun value amount => if amount.toNat < 64 then some (UInt64.shiftRight value (UInt64.ofNat amount.toNat)) else none

@[expose] public def checkedFromInt {α : Type} [Fixed α] (value : Int) : Option α :=
  if value < Fixed.minimum (α := α) then none else if Fixed.maximum (α := α) < value then none else some (Fixed.fromInt value)

@[expose] public def checkedConvert {α β : Type} [ToMathInt α] [Fixed β] (value : α) : Option β :=
  checkedFromInt (ToMathInt.toInt value)

@[expose] public def checkedAdd {α : Type} [Fixed α] (left right : α) : Option α :=
  checkedFromInt (ToMathInt.toInt left + ToMathInt.toInt right)

@[expose] public def checkedSubtract {α : Type} [Fixed α] (left right : α) : Option α :=
  checkedFromInt (ToMathInt.toInt left - ToMathInt.toInt right)

@[expose] public def checkedMultiply {α : Type} [Fixed α] (left right : α) : Option α :=
  checkedFromInt (ToMathInt.toInt left * ToMathInt.toInt right)

@[expose] public def checkedNegate {α : Type} [Fixed α] (value : α) : Option α :=
  checkedFromInt (-ToMathInt.toInt value)

@[expose] public def checkedQuotient {α : Type} [Fixed α] (left right : α) : Option α :=
  if ToMathInt.toInt right = 0 then none else checkedFromInt (Int.tdiv (ToMathInt.toInt left) (ToMathInt.toInt right))

@[expose] public def checkedAddInt64 (left right : Int64) : Option Int64 :=
  let value := left + right
  if (0 < right && value < left) || (right < 0 && left < value) then none else some value

@[expose] public def checkedSubtractInt64 (left right : Int64) : Option Int64 :=
  let value := left - right
  if (0 < right && left < value) || (right < 0 && value < left) then none else some value

@[expose] public def checkedNegateInt64 (value : Int64) : Option Int64 :=
  if value == (-9223372036854775808 : Int64) then none else some (-value)

public def magnitudeInt64 (value : Int64) : UInt64 :=
  let bits := value.toUInt64
  if value < 0 then 0 - bits else bits

public def signedMagnitudeInt64 (negative : Bool) (value : UInt64) : Int64 :=
  (if negative then 0 - value else value).toInt64

public def divideMagnitudeInt64 : Nat -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64
  | 0, _, _, _, quotient => quotient
  | Nat.succ fuel, source, divisor, remainder, quotient =>
      let high := 9223372036854775808 <= source
      let source := source + source
      let remainder := remainder + remainder + if high then 1 else 0
      let quotient := quotient + quotient
      if divisor <= remainder then
        divideMagnitudeInt64 fuel source divisor (remainder - divisor) (quotient + 1)
      else
        divideMagnitudeInt64 fuel source divisor remainder quotient

@[expose] public def checkedQuotientInt64 (left right : Int64) : Option Int64 :=
  if right == 0 then none
  else if left == (-9223372036854775808 : Int64) && right == (-1 : Int64) then none
  else
    let negative := (left < 0) != (right < 0)
    some (signedMagnitudeInt64 negative
      (divideMagnitudeInt64 64 (magnitudeInt64 left) (magnitudeInt64 right) 0 0))

public def multiplyMagnitudeInt64 : Nat -> UInt64 -> UInt64 -> UInt64 -> Bool -> Option UInt64
  | 0, _, _, accumulator, _ => some accumulator
  | Nat.succ fuel, source, multiplicand, accumulator, negative =>
      let high := 9223372036854775808 <= source
      let limit := if negative then 9223372036854775808 else 9223372036854775807
      let halfLimit := if negative then 4611686018427387904 else 4611686018427387903
      if halfLimit < accumulator then none
      else
        let doubled := accumulator + accumulator
        if high then
          if limit < multiplicand || limit - multiplicand < doubled then none
          else multiplyMagnitudeInt64 fuel (source + source) multiplicand
            (doubled + multiplicand) negative
        else
          multiplyMagnitudeInt64 fuel (source + source) multiplicand doubled negative

@[expose] public def checkedMultiplyInt64 (left right : Int64) : Option Int64 :=
  let negative := (left < 0) != (right < 0)
  match multiplyMagnitudeInt64 64 (magnitudeInt64 right) (magnitudeInt64 left) 0 negative with
  | none => none
  | some value => some (signedMagnitudeInt64 negative value)

@[noinline] public def subtract {α : Type} [Sub α] (left right : α) : α := left - right
@[noinline] public def multiply {α : Type} [Mul α] (left right : α) : α := left * right
@[noinline] public def negate {α : Type} [Neg α] (value : α) : α := -value

public class Quotient (α : Type) where
  quotient : α -> α -> α
  remainder : α -> α -> α
  isZero : α -> Bool

public instance : Quotient Nat where
  quotient := Nat.div
  remainder := Nat.mod
  isZero := fun value => value == 0

public instance : Quotient Int where
  quotient := Int.tdiv
  remainder := Int.tmod
  isZero := fun value => value == 0

@[noinline] public def quotient {α : Type} [Quotient α] (left right zeroCase : α) : α :=
  if Quotient.isZero right then zeroCase else Quotient.quotient left right

@[noinline] public def remainder {α : Type} [Quotient α] (left right zeroCase : α) : α :=
  if Quotient.isZero right then zeroCase else Quotient.remainder left right

@[expose] public def bitAnd {α : Type} [Fixed α] (left right : α) : α := Fixed.bitAnd left right
@[expose] public def bitOr {α : Type} [Fixed α] (left right : α) : α := Fixed.bitOr left right
@[expose] public def bitXor {α : Type} [Fixed α] (left right : α) : α := Fixed.bitXor left right
@[expose] public def bitNot {α : Type} [Fixed α] (value : α) : α := Fixed.bitNot value
@[expose] public def shiftLeft {α : Type} [Fixed α] (value : α) (amount : UInt32) : Option α := Fixed.shiftLeft value amount
@[expose] public def shiftRight {α : Type} [Fixed α] (value : α) (amount : UInt32) : Option α := Fixed.shiftRight value amount

public class Appendable (α : Type) where append : α -> α -> α
public instance {α : Type} : Appendable (List α) where append := List.append
public instance : Appendable ByteArray where append := ByteArray.append
@[noinline] public def append {α : Type} [Appendable α] (left right : α) : α := Appendable.append left right

public class Lengthable (α : Type) where length : α -> Nat
public instance {α : Type} : Lengthable (List α) where length := List.length
public instance : Lengthable ByteArray where length := ByteArray.size
public instance : Lengthable String where length := String.length
@[noinline] public def length {α : Type} [Lengthable α] (value : α) : Nat := Lengthable.length value

@[expose] public def listIndex {α : Type} : List α -> Nat -> Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: tail, index + 1 => listIndex tail index

public class Indexable (α β : Type) where index : α -> Nat -> Option β
public instance {α : Type} : Indexable (List α) α where index := listIndex
public instance : Indexable ByteArray UInt8 where index := fun value offset => value.data[offset]?
@[noinline] public def index {α β : Type} [Indexable α β] (value : α) (offset : Nat) : Option β := Indexable.index value offset

public class Sliceable (α : Type) where slice : α -> Nat -> Nat -> Option α
public instance {α : Type} : Sliceable (List α) where
  slice := fun value start count => if start + count <= value.length then some ((value.drop start).take count) else none
public instance : Sliceable ByteArray where
  slice := fun value start count => if start + count <= value.size then some (value.extract start (start + count)) else none
@[noinline] public def slice {α : Type} [Sliceable α] (value : α) (start count : Nat) : Option α := Sliceable.slice value start count

@[noinline] public def utf8Encode (value : String) : ByteArray := value.toUTF8
@[noinline] public def utf8Decode (value : ByteArray) : Option String := String.fromUTF8? value
@[noinline] public def compareBytes (left right : ByteArray) : Ordering := compare left.toList right.toList
@[expose] public def equal {α : Type} [BEq α] (left right : α) : Bool := left == right

@[noinline] public def splitExact (value delimiter : String) (maximum : UInt32) : Option (List String) :=
  let fields := value.splitOn delimiter
  if delimiter.isEmpty || maximum.toNat < fields.length then none else some fields

@[noinline] public def join (values : List String) (delimiter : String) : String := delimiter.intercalate values

public class Decimal (α : Type) where
  parse : String -> Option α
  format : α -> String

public instance : Decimal Int where
  parse := fun value => match value.toInt? with | some parsed => if toString parsed = value then some parsed else none | none => none
  format := toString

public instance {α : Type} [Fixed α] [ToString α] : Decimal α where
  parse := fun value => match value.toInt? with | some parsed => if toString parsed = value then checkedFromInt parsed else none | none => none
  format := toString

@[noinline] public def parseDecimal {α : Type} [Decimal α] (value : String) : Option α := Decimal.parse value
@[noinline] public def formatDecimal {α : Type} [Decimal α] (value : α) : String := Decimal.format value

end LexLeanRuntime
"#
}

/// Render one semantic module as prose-free Lean.
pub fn render_lean(
    checked: &CheckedModule,
    module: &SemanticModule,
    module_prefix: &str,
) -> Result<Emitter, Diagnostic> {
    let render = Render {
        prefix: module_prefix,
    };
    let document = &checked.document;
    let mut text = String::from("module\npublic import Init\n");
    for import in &document.imports {
        text.push_str(&format!("public import {module_prefix}.{import}\n"));
    }
    text.push_str("set_option autoImplicit false\nnamespace ");
    text.push_str(&document.lean_module);
    text.push('\n');
    if serde_json::to_string(module)
        .expect("semantic module serialization")
        .contains("\"kind\":\"primitive\"")
    {
        text.push_str(portable_runtime());
    }
    for declaration in &module.declarations {
        text.push('\n');
        match declaration {
            SemanticDeclaration::Structure {
                name,
                type_parameters,
                parameters,
                fields,
            } => {
                text.push_str(&format!(
                    "public structure {name}{}{} where\n",
                    render.type_parameters(type_parameters),
                    render.parameters(parameters)
                ));
                for field in fields {
                    text.push_str(&format!(
                        "  {} : {}\n",
                        field.name,
                        render.ty(&field.r#type)
                    ));
                }
            }
            SemanticDeclaration::Class {
                name,
                type_parameters,
                parameters,
                fields,
            } => {
                text.push_str(&format!(
                    "public class {name}{}{} where\n",
                    render.type_parameters(type_parameters),
                    render.parameters(parameters)
                ));
                for field in fields {
                    text.push_str(&format!(
                        "  {} : {}\n",
                        field.name,
                        render.ty(&field.r#type)
                    ));
                }
            }
            SemanticDeclaration::Instance {
                name,
                class,
                arguments,
                priority,
                fields,
            } => {
                let arguments = arguments
                    .iter()
                    .map(|argument| format!(" ({})", render.ty(argument)))
                    .collect::<String>();
                text.push_str(&format!(
                    "public instance (priority := {priority}) {name} : {}{arguments} where\n",
                    render.member(class)
                ));
                for field in fields {
                    text.push_str(&format!(
                        "  {} := {}\n",
                        field.field,
                        render.term(&field.value)
                    ));
                }
            }
            SemanticDeclaration::Inductive {
                name,
                type_parameters,
                parameters,
                constructors,
            } => {
                text.push_str(&format!(
                    "public inductive {name}{}{} where\n",
                    render.type_parameters(type_parameters),
                    render.parameters(parameters)
                ));
                for constructor in constructors {
                    let fields = constructor
                        .fields
                        .iter()
                        .map(|field| format!(" (_ : {})", render.ty(field)))
                        .collect::<String>();
                    text.push_str(&format!("  | {}{fields}\n", constructor.name));
                }
            }
            SemanticDeclaration::Definition {
                name,
                parameters,
                result,
                body,
                recursive_argument,
                ..
            } => {
                if let Some(recursive_argument) = recursive_argument {
                    let equations = render
                        .recursive_equations(name, parameters, result, recursive_argument, body)
                        .ok_or_else(|| {
                            Diagnostic::new(
                                code!("LLI9001"),
                                "phase lean-backend: recursive definition is not a top-level structural match",
                            )
                        })?;
                    text.push_str(&equations);
                } else {
                    text.push_str(&format!(
                        "@[expose] public def {name}{} : {} := {}\n",
                        render.parameters(parameters),
                        render.ty(result),
                        render.term(body)
                    ));
                }
            }
            SemanticDeclaration::Theorem {
                name,
                parameters,
                statement,
                proof,
                ..
            } => {
                text.push_str(&format!(
                    "public theorem {name}{} : {} := by\n{}",
                    render.parameters(parameters),
                    render.term(statement),
                    render.proof(proof, 1)
                ));
            }
        }
    }
    text.push_str("\nend ");
    text.push_str(&document.lean_module);
    text.push('\n');
    if text.contains("--") {
        return Err(Diagnostic::new(
            code!("LLI9001"),
            "phase lean-backend: semantic lowering produced a comment token",
        ));
    }
    Ok(emit(checked, &text, "semantic-lean-module"))
}

fn tex_escape(text: &str) -> String {
    let mut out = String::new();
    for character in text.chars() {
        match character {
            '\\' => out.push_str("\\textbackslash{}"),
            '{' => out.push_str("\\{"),
            '}' => out.push_str("\\}"),
            '#' => out.push_str("\\#"),
            '$' => out.push_str("\\$"),
            '%' => out.push_str("\\%"),
            '&' => out.push_str("\\&"),
            '_' => out.push_str("\\_"),
            '^' => out.push_str("\\^{}"),
            '~' => out.push_str("\\~{}"),
            other if other.is_ascii() => out.push(other),
            other => out.push_str(&format!("<U+{:04X}>", u32::from(other))),
        }
    }
    out
}

/// Render the same semantic module as canonical explanatory LaTeX.
pub fn render_latex(
    checked: &CheckedModule,
    module: &SemanticModule,
    module_prefix: &str,
) -> Result<Emitter, Diagnostic> {
    let render = Render {
        prefix: module_prefix,
    };
    let mut text = String::from(
        "\\documentclass[11pt]{article}\n\\usepackage[T1]{fontenc}\n\\usepackage{amsmath,amssymb}\n\\begin{document}\n\\section*{Semantic declarations}\n",
    );
    for declaration in &module.declarations {
        text.push_str(&format!(
            "\\subsection*{{\\texttt{{{}}}}}\n\\noindent Kind: \\texttt{{{}}}.\\par\n",
            tex_escape(declaration.name()),
            declaration.kind()
        ));
        match declaration {
            SemanticDeclaration::Definition {
                result,
                body,
                axioms,
                ..
            } => {
                let policy = if axioms.is_empty() {
                    "none".to_owned()
                } else {
                    format!("exact [{}]", axioms.join(", "))
                };
                text.push_str(&format!(
                    "\\noindent Type: \\texttt{{{}}}.\\par\n\\noindent Definition: \\texttt{{{}}}.\\par\n\\noindent Axiom policy: \\texttt{{{}}}.\\par\n",
                    tex_escape(&render.ty(result)),
                    tex_escape(&render.term(body)),
                    tex_escape(&policy)
                ));
            }
            SemanticDeclaration::Theorem {
                statement, axioms, ..
            } => {
                let policy = if axioms.is_empty() {
                    "none".to_owned()
                } else {
                    format!("exact [{}]", axioms.join(", "))
                };
                text.push_str(&format!(
                    "\\noindent Statement: \\texttt{{{}}}.\\par\n\\noindent Axiom policy: \\texttt{{{}}}.\\par\n",
                    tex_escape(&render.term(statement)),
                    tex_escape(&policy)
                ));
            }
            _ => {}
        }
    }
    text.push_str("\\end{document}\n");
    Ok(emit(checked, &text, "semantic-latex-module"))
}
