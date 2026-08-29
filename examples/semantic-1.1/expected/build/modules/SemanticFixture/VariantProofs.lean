module
public import Init
set_option autoImplicit false
namespace SemanticFixture.VariantProofs

public structure ReflectionPair where
  left : Nat
  right : Nat

@[expose] public def validatePair (pair : ReflectionPair) : Bool := ((Nat.beq ((pair).left) (0)) && (Nat.beq ((pair).right) (1)))

@[expose] public def pairValid (pair : ReflectionPair) : Prop := (((pair).left = 0) /\ ((pair).right = 1))

public theorem pair_sound_complete (pair : ReflectionPair) : ((validatePair (pair) = true) <-> pairValid (pair)) := by
  have llAndBridge : ∀ left right : Bool, ((left && right) = true) ↔ left = true ∧ right = true := by
    intro left right
    cases left <;> cases right <;> decide
  have llBeqRefl : ∀ value : Nat, Nat.beq value value = true := by
    intro value
    induction value with
    | zero => rfl
    | succ value ih => exact ih
  have llBeqBridge : ∀ left right : Nat, Nat.beq left right = true ↔ left = right := by
    intro left right
    constructor
    · exact Nat.eq_of_beq_eq_true
    · intro h
      cases h
      exact llBeqRefl left
  change (((Nat.beq ((pair).left) (0) && Nat.beq ((pair).right) (1))) = true) ↔ (((pair).left = 0) /\ ((pair).right = 1))
  exact Iff.trans (llAndBridge _ _) (and_congr (llBeqBridge _ _) (llBeqBridge _ _))

public theorem conjunction_refl : ((0 = 0) <-> (0 = 0)) := by
  constructor
  ·
    decide
  ·
    decide

public theorem congruence_refl (value : Nat) : ((value + 0) = (value + 0)) := by
  congr 1

public theorem conjunction_reused : ((0 = 0) <-> (0 = 0)) := by
  exact conjunction_refl

end SemanticFixture.VariantProofs
