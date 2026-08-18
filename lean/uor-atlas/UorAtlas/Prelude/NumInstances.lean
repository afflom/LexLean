module
public import Init
public import UorAtlas.Prelude.Algebra

/-!
`Z` and `Q` as objects of the `UorAtlas.Prelude` hierarchy, together with the two
statements of UOR-ATLAS-FORMAL-001 that are facts about fields rather than about
the Atlas: the ambient lemma `FI1` of section 19.6, and section 19.3's `A1`,
which that section insists is *derived, not assumed*.

Section 0 fixes `Q` as the common source of every `iota_v : Q -> Qv(v)`, and
`Z` as the ring the lattice `L` of `D10` lives over, so those two carriers are
where the abstract hierarchy of `UorAtlas.Prelude.Algebra` has to touch ground.
Both are Lean core types with a complete set of core lemmas; nothing here
reproves arithmetic, it only records which core lemma discharges which field.

`A1` is derived here for an arbitrary nonzero commutative-ring target rather
than for `RR` and `Q_p` specifically. That is deliberate and is what lets the
place layer avoid constructing the completions at all: section 19.3 says the
only thing used about `Qv(v)` is that it is a nonzero ring receiving a ring
homomorphism from `Q`, and that is exactly the hypothesis `A1` carries.
-/

set_option autoImplicit false

namespace UorAtlas.Prelude.NumInstances

universe u v

open AddCommGroup CommRing Field

/-! ## `Z` and `Q` as objects of the hierarchy -/

/-- `Z` as the additive group underlying `D9`'s ambient `Z^O`. -/
public instance instAddCommGroupInt : AddCommGroup Int where
  zero := 0
  add := (· + ·)
  neg := (- ·)
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  add_zero := Int.add_zero
  add_neg := Int.add_right_neg

/-- `Z` as a commutative ring. Sharing `toAddCommGroup` with
`instAddCommGroupInt` keeps the two instances the *same* additive structure, so
no diamond can arise between `AddCommGroup Int` found directly and the one found
through `CommRing.toAddCommGroup`. -/
public instance instCommRingInt : CommRing Int where
  toAddCommGroup := instAddCommGroupInt
  one := 1
  mul := (· * ·)
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  left_distrib := Int.mul_add

/-- `Q` as an additive group: the carrier `V` of `D34` is a `Q`-module. -/
public instance instAddCommGroupRat : AddCommGroup Rat where
  zero := 0
  add := (· + ·)
  neg := (- ·)
  add_assoc := Rat.add_assoc
  add_comm := Rat.add_comm
  add_zero := Rat.add_zero
  add_neg := Rat.add_neg_cancel

/-- `Q` as a commutative ring, sharing its additive structure with
`instAddCommGroupRat` for the same reason as `instCommRingInt`. -/
public instance instCommRingRat : CommRing Rat where
  toAddCommGroup := instAddCommGroupRat
  one := 1
  mul := (· * ·)
  mul_assoc := Rat.mul_assoc
  mul_comm := Rat.mul_comm
  one_mul := Rat.one_mul
  left_distrib := Rat.mul_add

/-- `Q` as a field. This is the instance `A1` consumes: it is the *field*
hypothesis of `FI1`, and it is the only reason `A1` is a theorem rather than an
assumption. -/
public instance instFieldRat : Field Rat where
  toCommRing := instCommRingRat
  inv := (·⁻¹)
  one_ne_zero := by decide
  mul_inv_cancel := Rat.mul_inv_cancel

/-! ## Consequences of the ring axioms

`UorAtlas.Prelude.Algebra` states the axioms in their minimal form, so the
standard companions (`0 + a = a`, `a * 0 = 0`, cancellation) are theorems and
have to be proved once before `FI1` can use them. -/

section CommRingLemmas

variable {R : Type u} [CommRing R]

/-- The step that turns a kernel membership back into an equation. -/
public theorem eq_of_add_neg_eq_zero {a b : R} (h : add a (neg b) = zero) : a = b := by
  have h' : add (add a (neg b)) b = add zero b := by rw [h]
  rwa [add_assoc, neg_add_cancel, add_zero, zero_add] at h'

end CommRingLemmas

/-! ## Ring homomorphisms -/

section RingHomLemmas

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

public theorem ringHom_map_zero (f : RingHom R S) : f.toFun zero = (zero : S) :=
  add_left_cancel <|
    calc add (f.toFun zero) (f.toFun zero)
        = f.toFun (add zero zero) := (f.map_add zero zero).symm
      _ = f.toFun zero := by rw [add_zero]
      _ = add (f.toFun zero) zero := (add_zero _).symm

public theorem ringHom_map_neg (f : RingHom R S) (a : R) :
    f.toFun (neg a) = neg (f.toFun a) := by
  refine add_left_cancel (a := f.toFun a) ?_
  rw [← f.map_add, add_neg, add_neg, ringHom_map_zero]

end RingHomLemmas

/-- The canonical `Z -> Q`. Section 13 localises the single rational carrier
`V = L (x)_Z Q` of `D34`, and this is the structure map along which that
extension of scalars is taken.

`@[expose]` because importing modules must be able to reduce `intToRat.toFun n`
to the core cast; with the body sealed, `rfl` on a concrete integer fails. -/
@[expose] public def intToRat : RingHom Int Rat where
  toFun n := (n : Rat)
  map_one := Rat.intCast_one
  map_add := Rat.intCast_add
  map_mul := Rat.intCast_mul

/-! ## `FI1` and `A1` -/

/-- An ideal of a commutative ring. Section 19.3 argues `A1` through the kernel
of a ring homomorphism *as an ideal*, so the notion is introduced rather than
short-circuited: `Ideal.mem_all_of_mem_ne_zero` is the step "a field has only
the two ideals", and that step is a statement about ideals, not about kernels. -/
public structure Ideal (R : Type u) [CommRing R] where
  mem : R → Prop
  zero_mem : mem zero
  add_mem : ∀ {a b : R}, mem a → mem b → mem (add a b)
  mul_mem : ∀ (r : R) {a : R}, mem a → mem (mul r a)

/-- The kernel of a ring homomorphism, as an ideal of its source. `@[expose]`
for the same reason as `intToRat`: `(ker f).mem a` is only usable downstream if
it still reduces to `f a = 0`. -/
@[expose] public def ker {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : RingHom R S) : Ideal R where
  mem a := f.toFun a = zero
  zero_mem := ringHom_map_zero f
  add_mem := by
    intro a b ha hb
    show f.toFun (add a b) = zero
    rw [f.map_add, ha, hb, add_zero]
  mul_mem := by
    intro r a ha
    show f.toFun (mul r a) = zero
    rw [f.map_mul, ha, mul_zero]

/-- "A field has only the two ideals", in the half `FI1` consumes: an ideal
containing a nonzero element is the whole field. Stating the dichotomy as a
disjunction would need excluded middle to case on, and its other disjunct is
just the failure of this hypothesis, so nothing is lost by taking the implication. -/
public theorem Ideal.mem_all_of_mem_ne_zero {K : Type u} [Field K] (I : Ideal K)
    {a : K} (ha : I.mem a) (h : a ≠ zero) (x : K) : I.mem x := by
  have hx : mul (mul x (inv a)) a = x := by
    rw [mul_assoc, mul_comm (inv a) a, mul_inv_cancel a h, mul_one]
  exact hx ▸ I.mul_mem (mul x (inv a)) ha

/-- `FI1` (section 19.6): a ring homomorphism from a field to a nonzero ring is
injective.

The proof is the document's: the kernel is an ideal (`ker`), a field has only
the two ideals (`Ideal.mem_all_of_mem_ne_zero`), and `1 |-> 1 != 0` excludes the
improper one. Nonzero-ness of the target is taken in its ring form, `1 != 0`,
which is what "nonzero ring" means and what the `1 |-> 1` clause needs. -/
public theorem FI1 {K : Type u} {S : Type v} [Field K] [CommRing S]
    (hS : (one : S) ≠ zero) (f : RingHom K S) : Function.Injective f.toFun := by
  intro a b hab
  have hker : (ker f).mem (add a (neg b)) := by
    show f.toFun (add a (neg b)) = zero
    rw [f.map_add, ringHom_map_neg f, hab, add_neg]
  refine eq_of_add_neg_eq_zero (Classical.byContradiction fun hne => ?_)
  have hone : f.toFun (one : K) = (zero : S) :=
    (ker f).mem_all_of_mem_ne_zero hker hne one
  exact hS (f.map_one.symm.trans hone)

/-- `A1` (section 19.3): the canonical map out of `Q` into a nonzero commutative
ring is injective, so `iota_v : Q -> Qv(v)` is injective for every place `v`.

Section 19.1 records `A1` as `DERIVED`, and this is that derivation: it is
`FI1` at the field `Q`, with no property of `RR` or `Q_p` used beyond being a
nonzero ring that receives a ring homomorphism. -/
public theorem A1 {S : Type u} [CommRing S] (hS : (one : S) ≠ zero) (f : RingHom Rat S) :
    Function.Injective f.toFun :=
  FI1 hS f

end UorAtlas.Prelude.NumInstances
