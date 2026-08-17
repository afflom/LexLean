module
public import Init
public import PeanoArithmetic.Addition
set_option autoImplicit false
namespace PeanoArithmetic.Order

@[expose] public def positive (llv0 : Nat) : Prop :=
  Nat.lt 0 llv0

public theorem successor_positive (llv0 : Nat) : PeanoArithmetic.Order.positive (Nat.succ llv0) := by
  exact Nat.zero_lt_succ llv0

public theorem zero_le (llv0 : Nat) : Nat.le 0 llv0 := by
  induction llv0 with
    | zero =>
      exact Nat.le_refl 0
    | succ llh0 llh1 =>
      exact Nat.le_trans llh1 (Nat.le_succ llh0)

public theorem le_add_right (llv0 : Nat) : Nat.le llv0 (Nat.add llv0 0) := by
  rw [PeanoArithmetic.Addition.add_zero llv0]
  exact Nat.le_refl llv0

public theorem zero_or_successor (llv0 : Nat) : Or (Eq llv0 (0 : Nat)) (Exists (fun (llv1 : Nat) => Eq llv0 (Nat.succ llv1))) := by
  cases llv0 with
    | zero =>
      left
      rfl
    | succ llh0 =>
      right
      refine ⟨llh0, ?_⟩
      rfl

public theorem successor_not_zero (llv0 : Nat) : Not (Eq (Nat.succ llv0) (0 : Nat)) := by
  intro llh0
  apply Nat.succ_ne_zero llv0
  exact llh0

end PeanoArithmetic.Order
