module
public import Init
public import SemanticFixture.KernelReductionProofs
public import SemanticFixture.Portable
public import SemanticFixture.PortableRecursion
public import SemanticFixture.Support
public import SemanticFixture.VariantInstances
public import SemanticFixture.VariantLogic
public import SemanticFixture.VariantProofs
public import SemanticFixture.VariantTerms
public import SemanticFixture.VariantTypes
set_option autoImplicit false
namespace SemanticFixture.Main

public inductive ComponentKind where
  | service
  | database

public structure Box (A : Type) where
  value : A

public structure Component where
  index : Nat
  kind : ComponentKind

public class Validatable where
  valid : Bool

public instance (priority := 1000) defaultValidatable : Validatable where
  valid := true

@[expose] public def sampleComponent : Component := ({ index := 0, kind := ComponentKind.service } : Component)

@[expose] public def allConsecutive : (expected : Nat) -> (values : List (Nat)) -> Bool
  | _expected, List.nil => true
  | expected, List.cons value rest => ((Nat.beq (expected) (value)) && allConsecutive ((expected + 1)) (rest))

@[expose] public def supportIsEnabled : Bool := SemanticFixture.Support.remoteEnabled

@[expose] public def Consecutive (values : List (Nat)) : Prop := (allConsecutive (0) (values) = true)

public theorem allConsecutive_sound_complete (values : List (Nat)) : ((allConsecutive (0) (values) = true) <-> Consecutive (values)) := by
  rfl

public theorem componentKind_refl (value : ComponentKind) : (value = value) := by
  cases value with
  | service =>
    rfl
  | database =>
    rfl

public theorem list_refl (values : List (Nat)) : (values = values) := by
  induction values with
  | nil =>
    rfl
  | cons head tail ih =>
    rfl

public theorem boolean_bridge : ((Nat.beq (0) (0)) = true) := by
  decide

public theorem empty_consecutive : (allConsecutive (0) (([] : List (Nat))) = true) := by
  simp only [allConsecutive]

end SemanticFixture.Main
