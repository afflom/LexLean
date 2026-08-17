module
public import Init
public import PeanoArithmetic.Addition
public import PeanoArithmetic.Divisibility
public import PeanoArithmetic.Doubling
public import PeanoArithmetic.Order
set_option autoImplicit false
namespace PeanoArithmetic.Main

public theorem comm_under_hypothesis (llv0 : Nat) (llv1 : Nat) : (Eq llv0 llv1) → Eq (Nat.add llv0 llv1) (Nat.add llv1 llv0) := by
  intro llh0
  exact PeanoArithmetic.Addition.add_comm llv0 llv1

public theorem comm_rewrite (llv0 : Nat) (llv1 : Nat) : (Eq llv0 llv1) → Eq (Nat.add llv0 llv0) (Nat.add llv1 llv0) := by
  intro llh0
  rw [llh0]

public theorem double_divides (llv0 : Nat) : PeanoArithmetic.Divisibility.divides 2 (PeanoArithmetic.Doubling.double llv0) := by
  refine ⟨llv0, ?_⟩
  exact Eq.symm (Nat.two_mul llv0)

public theorem even_divides (llv0 : Nat) : (PeanoArithmetic.Doubling.even llv0) → PeanoArithmetic.Divisibility.divides 2 llv0 := by
  intro llh0
  cases llh0 with
    | intro llh1 llh2 =>
      refine ⟨llh1, ?_⟩
      rw [llh2]
      exact Eq.symm (Nat.two_mul llh1)

public theorem even_or_not (llv0 : Nat) : Or (PeanoArithmetic.Doubling.even llv0) (Not (PeanoArithmetic.Doubling.even llv0)) := by
  exact Classical.em (PeanoArithmetic.Doubling.even llv0)

public theorem positive_or_zero (llv0 : Nat) : Or (PeanoArithmetic.Order.positive llv0) (Eq llv0 (0 : Nat)) := by
  cases llv0 with
    | zero =>
      right
      rfl
    | succ llh0 =>
      left
      exact PeanoArithmetic.Order.successor_positive llh0

end PeanoArithmetic.Main
