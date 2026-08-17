module
public import Init
public import PeanoArithmetic.Addition
set_option autoImplicit false
namespace PeanoArithmetic.Doubling

@[expose] public def count : Type :=
  Nat

@[expose] public def double (llv0 : Nat) : Nat :=
  Nat.add llv0 llv0

@[expose] public def even (llv0 : Nat) : Prop :=
  Exists (fun (llv1 : Nat) => Eq llv0 (Nat.add llv1 llv1))

public theorem double_even (llv0 : Nat) : PeanoArithmetic.Doubling.even (PeanoArithmetic.Doubling.double llv0) := by
  refine ⟨llv0, ?_⟩
  rfl

public theorem sum_even (llv0 : Nat) : PeanoArithmetic.Doubling.even (Nat.add llv0 llv0) := by
  refine ⟨llv0, ?_⟩
  rfl

public theorem zero_even : PeanoArithmetic.Doubling.even 0 := by
  refine ⟨(0 : Nat), ?_⟩
  rfl

public theorem even_succ_succ (llv0 : Nat) : (PeanoArithmetic.Doubling.even llv0) → PeanoArithmetic.Doubling.even (Nat.succ (Nat.succ llv0)) := by
  intro llh0
  cases llh0 with
    | intro llh1 llh2 =>
      refine ⟨Nat.succ llh1, ?_⟩
      rw [llh2, ← PeanoArithmetic.Addition.succ_add llh1 llh1]
      rfl

public theorem rotate (llv0 : Nat) (llv1 : Nat) : Eq (Nat.add llv0 (Nat.add llv1 (Nat.add llv0 llv1))) (Nat.add llv0 (Nat.add llv0 (Nat.add llv1 llv1))) := by
  rw [PeanoArithmetic.Addition.add_left_comm llv1 llv0 llv1]

public theorem double_add (llv0 : Nat) (llv1 : Nat) : Eq (PeanoArithmetic.Doubling.double (Nat.add llv0 llv1)) (Nat.add (PeanoArithmetic.Doubling.double llv0) (PeanoArithmetic.Doubling.double llv1)) := by
  calc (PeanoArithmetic.Doubling.double (Nat.add llv0 llv1)) = (Nat.add (Nat.add llv0 llv1) (Nat.add llv0 llv1)) := rfl
    _ = (Nat.add llv0 (Nat.add llv1 (Nat.add llv0 llv1))) := (Nat.add_assoc llv0 llv1 (Nat.add llv0 llv1))
    _ = (Nat.add llv0 (Nat.add llv0 (Nat.add llv1 llv1))) := (PeanoArithmetic.Doubling.rotate llv0 llv1)
    _ = (Nat.add (Nat.add llv0 llv0) (Nat.add llv1 llv1)) := (Eq.symm (Nat.add_assoc llv0 llv0 (Nat.add llv1 llv1)))
    _ = (Nat.add (PeanoArithmetic.Doubling.double llv0) (PeanoArithmetic.Doubling.double llv1)) := rfl

end PeanoArithmetic.Doubling
