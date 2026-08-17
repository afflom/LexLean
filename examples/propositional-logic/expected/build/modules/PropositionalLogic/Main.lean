module
public import Init
set_option autoImplicit false
namespace PropositionalLogic.Main

public theorem and_comm (llv0 : Prop) (llv1 : Prop) : (And llv0 llv1) → And llv1 llv0 := by
  intro llh0
  cases llh0 with
    | intro llh1 llh2 =>
      constructor
      exact llh2
      exact llh1

public theorem and_assoc (llv0 : Prop) (llv1 : Prop) (llv2 : Prop) : Iff (And (And llv0 llv1) llv2) (And llv0 (And llv1 llv2)) := by
  constructor
  intro llh0
  cases llh0 with
    | intro llh1 llh2 =>
      cases llh1 with
        | intro llh3 llh4 =>
          constructor
          exact llh3
          constructor
          exact llh4
          exact llh2
  intro llh5
  cases llh5 with
    | intro llh6 llh7 =>
      cases llh7 with
        | intro llh8 llh9 =>
          constructor
          constructor
          exact llh6
          exact llh8
          exact llh9

public theorem or_comm (llv0 : Prop) (llv1 : Prop) : (Or llv0 llv1) → Or llv1 llv0 := by
  intro llh0
  cases llh0 with
    | inl llh1 =>
      right
      exact llh1
    | inr llh2 =>
      left
      exact llh2

public theorem or_elim (llv0 : Prop) (llv1 : Prop) (llv2 : Prop) : (Or llv0 llv1) → (llv0 → llv2) → (llv1 → llv2) → llv2 := by
  intro llh0 llh1 llh2
  cases llh0 with
    | inl llh3 =>
      apply llh1
      exact llh3
    | inr llh4 =>
      apply llh2
      exact llh4

public theorem double_negation_intro (llv0 : Prop) : llv0 → Not (Not llv0) := by
  intro llh0
  intro llh1
  apply llh1
  exact llh0

public theorem de_morgan (llv0 : Prop) (llv1 : Prop) : (Not (Or llv0 llv1)) → And (Not llv0) (Not llv1) := by
  intro llh0
  constructor
  intro llh1
  apply llh0
  left
  exact llh1
  intro llh2
  apply llh0
  right
  exact llh2

public theorem explosion (llv0 : Prop) (llv1 : Prop) : (And llv0 (Not llv0)) → llv1 := by
  intro llh0
  cases llh0 with
    | intro llh1 llh2 =>
      exact absurd llh1 llh2

public theorem iff_refl (llv0 : Prop) : Iff llv0 llv0 := by
  constructor
  intro llh0
  exact llh0
  intro llh1
  exact llh1

public theorem iff_symm (llv0 : Prop) (llv1 : Prop) : (Iff llv0 llv1) → Iff llv1 llv0 := by
  intro llh0
  cases llh0 with
    | intro llh1 llh2 =>
      constructor
      exact llh2
      exact llh1

public theorem double_negation_elim (llv0 : Prop) : (Not (Not llv0)) → llv0 := by
  intro llh0
  cases (Classical.em llv0) with
    | inl llh1 =>
      exact llh1
    | inr llh2 =>
      exact absurd llh2 llh0

end PropositionalLogic.Main
