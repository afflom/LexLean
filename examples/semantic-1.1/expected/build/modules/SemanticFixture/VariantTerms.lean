module
public import Init
public import SemanticFixture.VariantTypes
set_option autoImplicit false
namespace SemanticFixture.VariantTerms

@[expose] public def boxedZero : SemanticFixture.VariantTypes.Box (Nat) := ({ value := 0 } : SemanticFixture.VariantTypes.Box (Nat))

@[expose] public def pairZeroOne : SemanticFixture.VariantTypes.PairNat := ({ left := 0, right := 1 } : SemanticFixture.VariantTypes.PairNat)

@[expose] public def leftOf (pair : SemanticFixture.VariantTypes.PairNat) : Nat := (pair).left

@[expose] public def someZero : SemanticFixture.VariantTypes.MaybeNat := SemanticFixture.VariantTypes.MaybeNat.some (0)

@[expose] public def chooseNat (flag : Bool) : Nat := (if flag then 0 else 1)

@[expose] public def lessEqualBool (left : Nat) (right : Nat) : Bool := (Nat.ble (left) (right))

@[expose] public def strictlyLessBool (left : Nat) (right : Nat) : Bool := (Nat.blt (left) (right))

@[expose] public def natDepth : (value : Nat) -> Nat
  | Nat.zero => 0
  | Nat.succ prior => (1 + natDepth (prior))

@[expose] public def maybeIsSome : (maybeValue : SemanticFixture.VariantTypes.MaybeNat) -> Bool
  | SemanticFixture.VariantTypes.MaybeNat.none => false
  | SemanticFixture.VariantTypes.MaybeNat.some _ => true

end SemanticFixture.VariantTerms
