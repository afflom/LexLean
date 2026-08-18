module
public import Init

/-!
The algebraic ambient UOR-ATLAS-FORMAL-001 quantifies over.

Lean's prelude carries `Nat`, `Int` and `Rat` as concrete types but no
algebraic hierarchy, and this library takes no dependency outside the
prelude. The document's ambient lemmas are stated over "a commutative
ring `A`" (`SD1`) and "a field" (`FI1`), so the hierarchy has to exist
before those lemmas can be *stated*, let alone proved.

It is deliberately minimal: exactly the structures section 19.6 names, and
no more. `BC1` is discharged by parameterizing section 13 over a
commutative ring rather than by constructing `Z_p`, which is why there is
a `CommRing` class here and no completion machinery anywhere.
-/

set_option autoImplicit false

namespace UorAtlas.Prelude

universe u v

/-- An additive commutative group: the ambient of every lattice in the document. -/
public class AddCommGroup (α : Type u) where
  zero : α
  add : α → α → α
  neg : α → α
  add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : α, add a b = add b a
  add_zero : ∀ a : α, add a zero = a
  add_neg : ∀ a : α, add a (neg a) = zero

/-- A commutative ring with unit: the `A` of `SD1`, and the parameter of the
place layer that lets `BC1` avoid a constructed `Z_p`. -/
public class CommRing (α : Type u) extends AddCommGroup α where
  one : α
  mul : α → α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : α, mul a b = mul b a
  one_mul : ∀ a : α, mul one a = a
  left_distrib : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)

/-- A field: `FI1` speaks of a ring homomorphism *from a field*, so the
distinction from `CommRing` is load-bearing rather than decorative. -/
public class Field (α : Type u) extends CommRing α where
  inv : α → α
  one_ne_zero : one ≠ (zero : α)
  mul_inv_cancel : ∀ a : α, a ≠ zero → mul a (inv a) = one

/-- A homomorphism of commutative rings. `RH1` is the statement that such a
map commutes with any integer-polynomial expression; `FI1` is that it is
injective when its source is a field. -/
public structure RingHom (R : Type u) (S : Type v) [CommRing R] [CommRing S] where
  toFun : R → S
  map_one : toFun CommRing.one = CommRing.one
  map_add : ∀ a b, toFun (AddCommGroup.add a b) = AddCommGroup.add (toFun a) (toFun b)
  map_mul : ∀ a b, toFun (CommRing.mul a b) = CommRing.mul (toFun a) (toFun b)

end UorAtlas.Prelude
