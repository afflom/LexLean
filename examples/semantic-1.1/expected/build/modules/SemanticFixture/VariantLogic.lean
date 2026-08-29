module
public import Init
set_option autoImplicit false
namespace SemanticFixture.VariantLogic

@[expose] public def ordered (left : Nat) (right : Nat) : Prop := (left <= right)

@[expose] public def strictlyOrdered (left : Nat) (right : Nat) : Prop := (left < right)

@[expose] public def boolExcludedMiddle (flag : Bool) : Bool := (flag || (!flag))

@[expose] public def logicalLaw (n : Nat) : Prop := (((n = n) -> (n = n)) <-> ((n = n) -> (n = n)))

@[expose] public def allReflexive : Prop := (forall (n : Nat), (n = n))

@[expose] public def propConjunction : Prop := ((0 = 0) /\ (0 < 1))

end SemanticFixture.VariantLogic
