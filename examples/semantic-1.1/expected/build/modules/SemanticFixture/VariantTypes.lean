module
public import Init
set_option autoImplicit false
namespace SemanticFixture.VariantTypes

public inductive MaybeNat where
  | none
  | some (_ : Nat)

public structure Box (A : Type) where
  value : A

public structure PairNat where
  left : Nat
  right : Nat

public class DefaultValue (A : Type) where
  default : A

public instance (priority := 1000) natDefault : DefaultValue (Nat) where
  default := 0

@[expose] public def identityType (T : Type) : Type := T

@[expose] public def unitValue : Unit := ()

@[expose] public def singletonZero : List (Nat) := (0 :: ([] : List (Nat)))

end SemanticFixture.VariantTypes
