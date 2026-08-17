module
public import Init
set_option autoImplicit false
namespace PeanoArithmetic.Addition

public theorem add_zero (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by
  rfl

public theorem zero_add (llv0 : Nat) : Eq (Nat.add 0 llv0) llv0 := by
  exact Nat.zero_add llv0

public theorem succ_add (llv0 : Nat) (llv1 : Nat) : Eq (Nat.add (Nat.succ llv0) llv1) (Nat.succ (Nat.add llv0 llv1)) := by
  exact Nat.succ_add llv0 llv1

public theorem both_identities (llv0 : Nat) : And (Eq (Nat.add llv0 0) llv0) (Eq (Nat.add 0 llv0) llv0) := by
  constructor
  rfl
  exact PeanoArithmetic.Addition.zero_add llv0

public theorem add_comm (llv0 : Nat) (llv1 : Nat) : Eq (Nat.add llv0 llv1) (Nat.add llv1 llv0) := by
  exact Nat.add_comm llv0 llv1

public theorem add_comm_symm (llv0 : Nat) (llv1 : Nat) : Eq (Nat.add llv1 llv0) (Nat.add llv0 llv1) := by
  exact Eq.symm (PeanoArithmetic.Addition.add_comm llv0 llv1)

public theorem add_assoc (llv0 : Nat) (llv1 : Nat) (llv2 : Nat) : Eq (Nat.add (Nat.add llv0 llv1) llv2) (Nat.add llv0 (Nat.add llv1 llv2)) := by
  exact Nat.add_assoc llv0 llv1 llv2

public theorem add_left_comm (llv0 : Nat) (llv1 : Nat) (llv2 : Nat) : Eq (Nat.add llv0 (Nat.add llv1 llv2)) (Nat.add llv1 (Nat.add llv0 llv2)) := by
  rw [← PeanoArithmetic.Addition.add_assoc llv0 llv1 llv2, PeanoArithmetic.Addition.add_comm llv0 llv1, PeanoArithmetic.Addition.add_assoc llv1 llv0 llv2]

end PeanoArithmetic.Addition
