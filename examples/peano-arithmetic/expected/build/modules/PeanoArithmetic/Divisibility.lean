module
public import Init
public import PeanoArithmetic.Addition
set_option autoImplicit false
namespace PeanoArithmetic.Divisibility

@[expose] public def divides (llv0 : Nat) (llv1 : Nat) : Prop :=
  Exists (fun (llv2 : Nat) => Eq llv1 (Nat.mul llv0 llv2))

public theorem divides_refl (llv0 : Nat) : PeanoArithmetic.Divisibility.divides llv0 llv0 := by
  refine ⟨(1 : Nat), ?_⟩
  exact Eq.symm (Nat.mul_one llv0)

public theorem one_divides (llv0 : Nat) : PeanoArithmetic.Divisibility.divides 1 llv0 := by
  refine ⟨llv0, ?_⟩
  exact Eq.symm (Nat.one_mul llv0)

public theorem divides_trans (llv0 : Nat) (llv1 : Nat) (llv2 : Nat) : (And (PeanoArithmetic.Divisibility.divides llv0 llv1) (PeanoArithmetic.Divisibility.divides llv1 llv2)) → PeanoArithmetic.Divisibility.divides llv0 llv2 := by
  intro llh0
  cases llh0 with
    | intro llh1 llh2 =>
      cases llh1 with
        | intro llh3 llh4 =>
          cases llh2 with
            | intro llh5 llh6 =>
              refine ⟨Nat.mul llh3 llh5, ?_⟩
              rw [llh6, llh4]
              exact Nat.mul_assoc llv0 llh3 llh5

end PeanoArithmetic.Divisibility
