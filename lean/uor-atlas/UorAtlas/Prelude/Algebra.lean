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

/-! ## The companions of the axioms

`AddCommGroup` and `CommRing` state their laws in minimal form --- `a + 0 = a`
but not `0 + a = a`, `1 * a = a` but not `a * 1 = a` --- so the mirrored forms
and the cancellation laws are theorems. They live here, beside the classes they
follow from, because every module below needs them and a second proof of a
settled fact is a second thing to keep true. -/

section Consequences

variable {α : Type u}

public theorem zero_add [AddCommGroup α] (a : α) :
    AddCommGroup.add AddCommGroup.zero a = a :=
  (AddCommGroup.add_comm AddCommGroup.zero a).trans (AddCommGroup.add_zero a)

public theorem neg_add_cancel [AddCommGroup α] (a : α) :
    AddCommGroup.add (AddCommGroup.neg a) a = AddCommGroup.zero :=
  (AddCommGroup.add_comm (AddCommGroup.neg a) a).trans (AddCommGroup.add_neg a)

public theorem add_left_cancel [AddCommGroup α] {a b c : α}
    (h : AddCommGroup.add a b = AddCommGroup.add a c) : b = c := by
  have h' := congrArg (AddCommGroup.add (AddCommGroup.neg a)) h
  rwa [← AddCommGroup.add_assoc, ← AddCommGroup.add_assoc, neg_add_cancel, zero_add,
    zero_add] at h'

/-- Double negation. Stated here rather than in a consumer: it is a fact about
`AddCommGroup` and nothing else, and it was previously proved twice --- once in
`Places` and once in `Functor` --- under two names, which is the shape the
duplication gate could not see until it began comparing conclusions. -/
public theorem neg_neg [AddCommGroup α] (a : α) :
    AddCommGroup.neg (AddCommGroup.neg a) = a :=
  add_left_cancel (a := AddCommGroup.neg a)
    ((AddCommGroup.add_neg (AddCommGroup.neg a)).trans (neg_add_cancel a).symm)

public theorem mul_zero [CommRing α] (a : α) :
    CommRing.mul a (AddCommGroup.zero : α) = AddCommGroup.zero :=
  add_left_cancel <|
    calc AddCommGroup.add (CommRing.mul a AddCommGroup.zero) (CommRing.mul a AddCommGroup.zero)
        = CommRing.mul a (AddCommGroup.add AddCommGroup.zero AddCommGroup.zero) :=
          (CommRing.left_distrib a AddCommGroup.zero AddCommGroup.zero).symm
      _ = CommRing.mul a AddCommGroup.zero := by rw [AddCommGroup.add_zero]
      _ = AddCommGroup.add (CommRing.mul a AddCommGroup.zero) AddCommGroup.zero :=
          (AddCommGroup.add_zero _).symm

public theorem zero_mul [CommRing α] (a : α) :
    CommRing.mul (AddCommGroup.zero : α) a = AddCommGroup.zero :=
  (CommRing.mul_comm AddCommGroup.zero a).trans (mul_zero a)

public theorem mul_one [CommRing α] (a : α) : CommRing.mul a CommRing.one = a :=
  (CommRing.mul_comm a CommRing.one).trans (CommRing.one_mul a)

end Consequences

/-- A homomorphism of commutative rings. `RH1` is the statement that such a
map commutes with any integer-polynomial expression; `FI1` is that it is
injective when its source is a field. -/
public structure RingHom (R : Type u) (S : Type v) [CommRing R] [CommRing S] where
  toFun : R → S
  map_one : toFun CommRing.one = CommRing.one
  map_add : ∀ a b, toFun (AddCommGroup.add a b) = AddCommGroup.add (toFun a) (toFun b)
  map_mul : ∀ a b, toFun (CommRing.mul a b) = CommRing.mul (toFun a) (toFun b)

end UorAtlas.Prelude
