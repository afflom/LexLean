module
public import Init
public import UorAtlas.Prelude.Algebra

/-!
Vectors, finite sums and matrices: the computational spine of the vendored
Atlas library.

This module owes `UOR-ATLAS-FORMAL-001` its four ring identities `M1`-`M4`
(section 19.2). Section 19.1 classifies them as `DECIDED` in the free
commutative ring "at size `O`", and sections 19.4/19.5 use them as the
premises of `F1`, `F3`, `F4`, `F5`, `F17`, `F19a`, `F22` and `T76a`, every one
of which is `DERIVED` **for every morphism** rather than on a generating set.
They are therefore proved here by induction over the dimension, at every size
rather than only at `O = 8`: the general statement subsumes the one the
document needs and keeps this module independent of the parameter layer that
fixes `O`.

Everything else here exists to make those proofs possible and to let later
modules evaluate concrete Atlas data -- `8`-dimensional integer vectors, `240`
roots, `120 x 120` integer matrices -- inside the kernel.
-/

set_option autoImplicit false

namespace UorAtlas.Prelude.Linear

open UorAtlas.Prelude.AddCommGroup
open UorAtlas.Prelude.CommRing

universe u v

variable {α : Type u} {β : Type v} {m n p q : Nat}

/-! ## The ambient algebra, as far as this module needs it

`Algebra.lean` states the classes and their defining equations; it derives
nothing from them, because nothing below the linear layer needed a derivation.
These are exactly the consequences the sum and matrix proofs below consume, and
no more. -/

section Group

variable [AddCommGroup α]

public theorem zero_add (a : α) : add zero a = a := by
  rw [add_comm]; exact add_zero a

public theorem add_left_comm (a b c : α) : add a (add b c) = add b (add a c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

public theorem add_add_add_comm (a b c d : α) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  rw [add_assoc, add_left_comm b c d, ← add_assoc]

public theorem add_right_cancel {a b c : α} (h : add a c = add b c) : a = b := by
  have h' : add (add a c) (neg c) = add (add b c) (neg c) := by rw [h]
  rwa [add_assoc, add_neg, add_zero, add_assoc, add_neg, add_zero] at h'

public theorem add_left_cancel {a b c : α} (h : add a b = add a c) : b = c :=
  add_right_cancel (by rw [add_comm b a, add_comm c a]; exact h)

public theorem neg_zero : neg (zero : α) = zero := by
  have h : add zero (neg zero) = (zero : α) := add_neg zero
  rwa [zero_add] at h

public theorem neg_add (a b : α) : neg (add a b) = add (neg a) (neg b) := by
  refine (add_left_cancel (a := add a b) ?_).symm
  rw [add_neg (add a b), add_add_add_comm, add_neg a, add_neg b, add_zero]

end Group

section Ring

variable [CommRing α]

public theorem mul_one (a : α) : mul a one = a := by
  rw [mul_comm]; exact one_mul a

public theorem mul_zero (a : α) : mul a zero = (zero : α) := by
  have hd : mul a (add zero zero) = add (mul a zero) (mul a zero) := left_distrib a zero zero
  rw [add_zero] at hd
  have h : add (mul a zero) zero = add (mul a zero) (mul a zero) := by rw [add_zero]; exact hd
  exact (add_left_cancel h).symm

public theorem zero_mul (a : α) : mul zero a = (zero : α) := by
  rw [mul_comm]; exact mul_zero a

public theorem right_distrib (a b c : α) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm (add a b) c, left_distrib, mul_comm c a, mul_comm c b]

public theorem neg_mul (a b : α) : mul (neg a) b = neg (mul a b) := by
  refine add_left_cancel (a := mul a b) ?_
  rw [← right_distrib, add_neg, zero_mul, add_neg]

end Ring

/-- Iterated addition: the value of a sum over a constant. -/
@[expose] public def nsmul [AddCommGroup α] : Nat → α → α
  | 0, _ => zero
  | k + 1, a => add a (nsmul k a)

/-! ## Vectors

`Vec n α` is the function type `Fin n → α`.

The alternative was an `Array`- or `List`-backed vector, and the choice was
decided on kernel reduction, which is the only evaluator that counts here:
proofs are replayed by the kernel, and the kernel is not the compiler.

* `Array` is the instinct carried over from compiled code, and it is the wrong
  one. The kernel has no primitive support for `Array`: it reduces through the
  `List` payload, so `Array.get` costs one recursor unfolding per index step
  and `Array.set` rebuilds the spine. Every operation is strictly slower than
  on the `List` underneath it.
* A `List`-backed vector drags a length invariant through every definition and
  every lemma, and it materialises intermediate data: a `120 x 120` product
  builds all `14400` entries even when the proof inspects one of them.
* The function representation is demand-driven. `Mat.mul`, `Mat.transpose` and
  `Mat.apply` below are definitional rearrangements that allocate nothing, so
  `Mat.mul A B i j` reduces exactly the entry asked for, and indexing is one
  beta step rather than a walk down a spine.

The price is that vector equality is function equality and so needs `funext`,
which charges `Quot.sound`. Where a later proof will rewrite with the
entrywise form instead, that form is stated separately as an `_apply` lemma,
which needs no `funext` and so charges no `Quot.sound`. -/
@[expose] public def Vec (n : Nat) (α : Type u) : Type u := Fin n → α

namespace Vec

/-- Vectors form an `AddCommGroup` pointwise. The group operations are left as
the class projections rather than given separate names such as `Vec.add`,
because a `Vec.add` would shadow the scalar `AddCommGroup.add` inside this
namespace and force every sum lemma to be written in fully qualified form. -/
public instance instAddCommGroup [AddCommGroup α] : AddCommGroup (Vec n α) where
  zero := fun _ => AddCommGroup.zero
  add x y := fun i => AddCommGroup.add (x i) (y i)
  neg x := fun i => AddCommGroup.neg (x i)
  add_assoc x y z := funext fun i => AddCommGroup.add_assoc (x i) (y i) (z i)
  add_comm x y := funext fun i => AddCommGroup.add_comm (x i) (y i)
  add_zero x := funext fun i => AddCommGroup.add_zero (x i)
  add_neg x := funext fun i => AddCommGroup.add_neg (x i)

public theorem add_apply [AddCommGroup α] (x y : Vec n α) (i : Fin n) :
    AddCommGroup.add x y i = AddCommGroup.add (x i) (y i) := rfl

public theorem neg_apply [AddCommGroup α] (x : Vec n α) (i : Fin n) :
    AddCommGroup.neg x i = AddCommGroup.neg (x i) := rfl

public theorem zero_apply [AddCommGroup α] (i : Fin n) :
    (AddCommGroup.zero : Vec n α) i = AddCommGroup.zero := rfl

/-- Scalar multiplication. Unlike the additive operations this has no ambient
class in `Algebra.lean`, so it keeps a name of its own. -/
@[expose] public def smul [CommRing α] (c : α) (x : Vec n α) : Vec n α :=
  fun i => CommRing.mul c (x i)

/-- Entrywise transport along a ring homomorphism: extension of scalars
(`D35`) read one coordinate at a time. -/
@[expose] public def map [CommRing α] [CommRing β] (φ : RingHom α β) (x : Vec n α) : Vec n β :=
  fun i => φ.toFun (x i)

/-- Deciding a vector equation is deciding `n` scalar equations.
`Fin.decidableForallFin` reduces structurally, so `decide` on concrete Atlas
data does not descend into well-founded recursion. -/
public instance instDecidableEq [DecidableEq α] : DecidableEq (Vec n α) :=
  fun x y =>
    decidable_of_decidable_of_iff (p := ∀ i, x i = y i)
      (Iff.intro funext (fun h i => congrFun h i))

end Vec

/-! ## Finite sums -/

namespace Vec

/-- The sum over `Fin n` in an arbitrary `AddCommGroup`.

The recursion peels the **first** index and re-indexes the tail through
`Fin.succ`. That is what makes `sum_exchange` a three-line induction: the head
of a double sum is itself a whole inner sum, so Fubini needs only `sum_add`
and the inductive hypothesis and never touches index arithmetic. -/
@[expose] public def sum [AddCommGroup α] : {n : Nat} → Vec n α → α
  | 0, _ => zero
  | _ + 1, v => add (v 0) (sum fun i => v i.succ)

section Sum

variable [AddCommGroup α]

public theorem sum_nil (v : Vec 0 α) : sum v = zero := rfl

public theorem sum_succ (v : Vec (n + 1) α) :
    sum v = add (v 0) (sum fun i => v i.succ) := rfl

public theorem sum_congr {x y : Vec n α} (h : ∀ i, x i = y i) : sum x = sum y := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sum_succ, h 0]
    exact congrArg _ (ih (fun i => h i.succ))

public theorem sum_const (c : α) : sum (n := n) (fun _ => c) = nsmul n c := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sum_succ]; exact congrArg _ ih

public theorem sum_zero : sum (n := n) (fun _ => (zero : α)) = zero := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sum_succ, ih]; exact add_zero zero

public theorem sum_add (x y : Vec n α) :
    sum (fun i => add (x i) (y i)) = add (sum x) (sum y) := by
  induction n with
  | zero => exact (add_zero zero).symm
  | succ k ih =>
    simp only [sum_succ]
    rw [ih (fun i => x i.succ) (fun i => y i.succ), add_add_add_comm]

/-- Splitting a sum along a decidable predicate. This is the form the document
splits sums in: `S22` and `S35` separate one fixed class set into an
AtlasInstance and its residue. Concatenation splitting over `Fin (m + n)` is
deliberately not stated -- the document never concatenates two index ranges,
it partitions a single one -- and it would drag `Nat.succ_add` casts through
every use. -/
public theorem sum_split (P : Fin n → Prop) [DecidablePred P] (x : Vec n α) :
    sum x = add (sum (fun i => if P i then x i else zero))
      (sum (fun i => if P i then zero else x i)) := by
  rw [← sum_add]
  refine sum_congr (fun i => ?_)
  refine Decidable.byCases (p := P i) ?_ ?_
  · intro hi; rw [if_pos hi, if_pos hi, add_zero]
  · intro hi; rw [if_neg hi, if_neg hi, zero_add]

public theorem sum_neg (x : Vec n α) : sum (fun i => neg (x i)) = neg (sum x) := by
  induction n with
  | zero => exact neg_zero.symm
  | succ k ih =>
    simp only [sum_succ]
    rw [ih (fun i => x i.succ), neg_add]

/-- Fubini for finite double sums. This is the lemma `M2` runs on. -/
public theorem sum_exchange (f : Fin m → Fin n → α) :
    sum (fun i => sum (fun j => f i j)) = sum (fun j => sum (fun i => f i j)) := by
  induction m with
  | zero => exact sum_zero.symm
  | succ k ih =>
    simp only [sum_succ]
    rw [ih (fun i j => f i.succ j), ← sum_add]

/-- A sum whose summand is supported at a single index. This is the whole
content of `M3`. -/
public theorem sum_ite_eq (i : Fin n) (x : Vec n α) :
    sum (fun k => if i = k then x k else zero) = x i := by
  induction n with
  | zero => exact i.elim0
  | succ k ih =>
    induction i using Fin.cases with
    | zero =>
      show add (if (0 : Fin (k + 1)) = 0 then x 0 else zero)
        (sum fun j => if (0 : Fin (k + 1)) = j.succ then x j.succ else zero) = x 0
      rw [if_pos rfl, sum_congr (y := fun _ => zero)
        (fun j => if_neg (Ne.symm (Fin.succ_ne_zero j))), sum_zero, add_zero]
    | succ i' =>
      have hc : ∀ j : Fin k, (if i'.succ = j.succ then x j.succ else zero)
          = (if i' = j then x j.succ else zero) := by
        refine fun j => Decidable.byCases (p := i' = j) ?_ ?_
        · intro hj; rw [if_pos (congrArg Fin.succ hj), if_pos hj]
        · intro hj; rw [if_neg (fun h => hj (Fin.succ_inj.mp h)), if_neg hj]
      show add (if i'.succ = 0 then x 0 else zero)
        (sum fun j => if i'.succ = j.succ then x j.succ else zero) = x i'.succ
      rw [if_neg (Fin.succ_ne_zero i'), sum_congr hc, ih i' (fun j => x j.succ), zero_add]

public theorem sum_ite_eq' (j : Fin n) (x : Vec n α) :
    sum (fun k => if k = j then x k else zero) = x j := by
  rw [← sum_ite_eq j x]
  refine sum_congr (fun k => ?_)
  refine Decidable.byCases (p := k = j) ?_ ?_
  · intro hk; rw [if_pos hk, if_pos hk.symm]
  · intro hk; rw [if_neg hk, if_neg (fun h => hk h.symm)]

end Sum

end Vec

/-! ## Sums in a commutative ring -/

namespace Vec

section SumRing

variable [CommRing α]

public theorem mul_sum (c : α) (x : Vec n α) :
    mul c (sum x) = sum (fun i => mul c (x i)) := by
  induction n with
  | zero => exact mul_zero c
  | succ k ih =>
    simp only [sum_succ]
    rw [left_distrib, ih (fun i => x i.succ)]

public theorem sum_mul (x : Vec n α) (c : α) :
    mul (sum x) c = sum (fun i => mul (x i) c) := by
  rw [mul_comm, mul_sum]
  exact sum_congr (fun i => mul_comm c (x i))

end SumRing

end Vec

/-! ## Ring homomorphisms and finite sums

`RH1` (section 19.6) is the ambient lemma that a ring homomorphism commutes
with any integer-polynomial expression. A finite sum of products is exactly
such an expression, and these two lemmas are the form in which `M1` and the
scalar extension of the bilinear form consume it. -/

public theorem hom_map_zero [CommRing α] [CommRing β] (φ : RingHom α β) :
    φ.toFun (zero : α) = (zero : β) := by
  have hd : φ.toFun (add (zero : α) zero) = add (φ.toFun (zero : α)) (φ.toFun zero) :=
    φ.map_add zero zero
  rw [add_zero] at hd
  have h : add (φ.toFun (zero : α)) zero = add (φ.toFun (zero : α)) (φ.toFun zero) := by
    rw [add_zero]; exact hd
  exact (add_left_cancel h).symm

public theorem hom_map_sum [CommRing α] [CommRing β] (φ : RingHom α β) (x : Vec n α) :
    φ.toFun (Vec.sum x) = Vec.sum (fun i => φ.toFun (x i)) := by
  induction n with
  | zero => exact hom_map_zero φ
  | succ k ih =>
    simp only [Vec.sum_succ]
    rw [φ.map_add, ih (fun i => x i.succ)]

/-! ## The integers

The document computes in exactly one ring: `D9`'s lattice sits in `Z^O`,
`D11`'s roots are integral, and `D55`'s Gram matrices are integer matrices.
`Algebra.lean` states the ambient classes and instantiates none of them, so
the instantiation is made here, in the first module that needs a concrete ring
to multiply matrices over. -/
public instance instCommRingInt : CommRing Int where
  zero := 0
  add := Int.add
  neg := Int.neg
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  add_zero := Int.add_zero
  add_neg := Int.add_right_neg
  one := 1
  mul := Int.mul
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  left_distrib := Int.mul_add

namespace Vec

/-- The sum over `Fin n` of integers, on `Int.add` directly.

`sum` reaches `Int.add` through two class projections at every step, and a
`120 x 120` product spends on the order of `120^3` steps there; the concrete
definition keeps that indirection off the kernel's hot path. `sumInt_eq_sum`
is the bridge, so no lemma has to be proved twice. -/
@[expose] public def sumInt : {n : Nat} → Vec n Int → Int
  | 0, _ => 0
  | _ + 1, v => v 0 + sumInt fun i => v i.succ

public theorem sumInt_eq_sum (v : Vec n Int) : sumInt v = sum v := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show v 0 + sumInt (fun i => v i.succ) = add (v 0) (sum fun i => v i.succ)
    exact congrArg (fun t => v 0 + t) (ih (fun i => v i.succ))

/-- The sum over `Fin n` of naturals. `Nat` has no negation, so it is not an
`AddCommGroup` and cannot borrow `sum` at all; the counting statements of the
document (`T5`, `T6`, `T7`, `D14`) are `Nat`-valued, so this is a definition in
its own right rather than a specialisation. -/
@[expose] public def sumNat : {n : Nat} → Vec n Nat → Nat
  | 0, _ => 0
  | _ + 1, v => v 0 + sumNat fun i => v i.succ

public theorem sumNat_congr {x y : Vec n Nat} (h : ∀ i, x i = y i) : sumNat x = sumNat y := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show x 0 + sumNat (fun i => x i.succ) = y 0 + sumNat fun i => y i.succ
    rw [h 0, ih (fun i => h i.succ)]

public theorem sumNat_add (x y : Vec n Nat) :
    sumNat (fun i => x i + y i) = sumNat x + sumNat y := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show x 0 + y 0 + sumNat (fun i => x i.succ + y i.succ)
      = (x 0 + sumNat fun i => x i.succ) + (y 0 + sumNat fun i => y i.succ)
    rw [ih (fun i => x i.succ) (fun i => y i.succ)]
    omega

public theorem sumNat_const (c : Nat) : sumNat (n := n) (fun _ => c) = n * c := by
  induction n with
  | zero => exact (Nat.zero_mul c).symm
  | succ k ih =>
    show c + sumNat (fun _ => c) = (k + 1) * c
    rw [ih, Nat.succ_mul, Nat.add_comm]

/-! ## The bilinear form -/

/-- The standard bilinear form `<-,->` of section 0, over an arbitrary
commutative ring rather than over `Z` alone: `D35a` defines the localised form
`<-,->_v` as the scalar extension of this one, and `inner_map` below is
precisely that statement. -/
@[expose] public def inner [CommRing α] (x y : Vec n α) : α :=
  sum (fun i => mul (x i) (y i))

section Inner

variable [CommRing α]

public theorem inner_comm (x y : Vec n α) : inner x y = inner y x :=
  sum_congr (fun i => mul_comm (x i) (y i))

public theorem inner_add_left (x y z : Vec n α) :
    inner (add x y) z = add (inner x z) (inner y z) := by
  have h : inner (add x y) z = sum (fun i => add (mul (x i) (z i)) (mul (y i) (z i))) :=
    sum_congr (fun i => right_distrib (x i) (y i) (z i))
  rw [h]
  exact sum_add (fun i => mul (x i) (z i)) (fun i => mul (y i) (z i))

public theorem inner_add_right (x y z : Vec n α) :
    inner x (add y z) = add (inner x y) (inner x z) := by
  rw [inner_comm x (add y z), inner_add_left, inner_comm y x, inner_comm z x]

public theorem inner_smul_left (c : α) (x y : Vec n α) :
    inner (smul c x) y = mul c (inner x y) := by
  show sum (fun i => mul (mul c (x i)) (y i)) = mul c (sum fun i => mul (x i) (y i))
  rw [mul_sum]
  exact sum_congr (fun i => mul_assoc c (x i) (y i))

public theorem inner_smul_right (c : α) (x y : Vec n α) :
    inner x (smul c y) = mul c (inner x y) := by
  rw [inner_comm x (smul c y), inner_smul_left, inner_comm y x]

public theorem inner_neg_left (x y : Vec n α) : inner (neg x) y = neg (inner x y) := by
  show sum (fun i => mul (neg (x i)) (y i)) = neg (sum fun i => mul (x i) (y i))
  rw [sum_congr (fun i => neg_mul (x i) (y i))]
  exact sum_neg (fun i => mul (x i) (y i))

public theorem inner_neg_right (x y : Vec n α) : inner x (neg y) = neg (inner x y) := by
  rw [inner_comm x (neg y), inner_neg_left, inner_comm y x]

/-- `D35a`: the localised form is the scalar extension of the rational one.
This is the vector-level companion of `M1`. -/
public theorem inner_map [CommRing β] (φ : RingHom α β) (x y : Vec n α) :
    φ.toFun (inner x y) = inner (map φ x) (map φ y) := by
  show φ.toFun (sum fun i => mul (x i) (y i))
    = sum (fun i => mul (φ.toFun (x i)) (φ.toFun (y i)))
  rw [hom_map_sum]
  exact sum_congr (fun i => φ.map_mul (x i) (y i))

end Inner

end Vec

/-- `<x,y>` on the integer lattice: the form of section 0 in the ring the
Atlas is actually computed in, on `Int.mul` and `Int.add` directly. -/
@[expose] public def dot (x y : Vec n Int) : Int := Vec.sumInt (fun i => x i * y i)

public theorem dot_eq_inner (x y : Vec n Int) : dot x y = Vec.inner x y :=
  Vec.sumInt_eq_sum _

public theorem dot_comm (x y : Vec n Int) : dot x y = dot y x := by
  rw [dot_eq_inner, dot_eq_inner]; exact Vec.inner_comm x y

public theorem dot_add_left (x y z : Vec n Int) :
    dot (add x y) z = dot x z + dot y z := by
  rw [dot_eq_inner, dot_eq_inner, dot_eq_inner]; exact Vec.inner_add_left x y z

public theorem dot_add_right (x y z : Vec n Int) :
    dot x (add y z) = dot x y + dot x z := by
  rw [dot_eq_inner, dot_eq_inner, dot_eq_inner]; exact Vec.inner_add_right x y z

public theorem dot_smul_left (c : Int) (x y : Vec n Int) :
    dot (Vec.smul c x) y = c * dot x y := by
  rw [dot_eq_inner, dot_eq_inner]; exact Vec.inner_smul_left c x y

public theorem dot_smul_right (c : Int) (x y : Vec n Int) :
    dot x (Vec.smul c y) = c * dot x y := by
  rw [dot_eq_inner, dot_eq_inner]; exact Vec.inner_smul_right c x y

public theorem dot_neg_left (x y : Vec n Int) : dot (neg x) y = -dot x y := by
  rw [dot_eq_inner, dot_eq_inner]; exact Vec.inner_neg_left x y

public theorem dot_neg_right (x y : Vec n Int) : dot x (neg y) = -dot x y := by
  rw [dot_eq_inner, dot_eq_inner]; exact Vec.inner_neg_right x y

/-! ## Matrices -/

/-- `Mat m n α`: `m` rows, each a `Vec n α`. -/
@[expose] public def Mat (m n : Nat) (α : Type u) : Type u := Fin m → Vec n α

namespace Mat

@[expose] public def mul [CommRing α] (A : Mat m n α) (B : Mat n p α) : Mat m p α :=
  fun i j => Vec.sum (fun k => CommRing.mul (A i k) (B k j))

@[expose] public def id [CommRing α] : Mat n n α :=
  fun i j => if i = j then CommRing.one else AddCommGroup.zero

@[expose] public def transpose (A : Mat m n α) : Mat n m α := fun i j => A j i

/-- Matrix negation is a named operation rather than an `AddCommGroup`
instance field, because `M4` cites it explicitly and the two minus signs of
`(-A)x = -(Ax)` live in different types: this one on `Mat`, the other on
`Vec`. -/
@[expose] public def neg [AddCommGroup α] (A : Mat m n α) : Mat m n α :=
  fun i j => AddCommGroup.neg (A i j)

@[expose] public def apply [CommRing α] (A : Mat m n α) (x : Vec n α) : Vec m α :=
  fun i => Vec.sum (fun j => CommRing.mul (A i j) (x j))

/-- Entrywise transport along a ring homomorphism: the matrix of a morphism
after extension of scalars (`D65`, `F2`). -/
@[expose] public def map [CommRing α] [CommRing β] (φ : RingHom α β) (A : Mat m n α) :
    Mat m n β := fun i j => φ.toFun (A i j)

public instance instDecidableEq [DecidableEq α] : DecidableEq (Mat m n α) :=
  fun A B =>
    decidable_of_decidable_of_iff (p := ∀ i, A i = B i)
      (Iff.intro funext (fun h i => congrFun h i))

/-- The literal shape section 19.2 means by "integer polynomials in the
entries": a sum of products of entries, every coefficient `1`. True by `rfl`. -/
public theorem mul_apply [CommRing α] (A : Mat m n α) (B : Mat n p α) (i : Fin m) (j : Fin p) :
    mul A B i j = Vec.sum (fun k => CommRing.mul (A i k) (B k j)) := rfl

public theorem id_apply [CommRing α] (i j : Fin n) :
    (id : Mat n n α) i j = if i = j then CommRing.one else AddCommGroup.zero := rfl

public theorem apply_apply [CommRing α] (A : Mat m n α) (x : Vec n α) (i : Fin m) :
    apply A x i = Vec.sum (fun j => CommRing.mul (A i j) (x j)) := rfl

public theorem transpose_transpose (A : Mat m n α) : transpose (transpose A) = A := rfl

public theorem transpose_mul [CommRing α] (A : Mat m n α) (B : Mat n p α) :
    transpose (mul A B) = mul (transpose B) (transpose A) := by
  funext j i
  exact Vec.sum_congr (fun k => CommRing.mul_comm (A i k) (B k j))

/-! The entrywise cores of `M2`, `M3`, `M1` and `M4`. They are stated
separately from the four labelled identities because they are equalities of
ring elements rather than of functions: they need no `funext`, so unlike
`M1`-`M4` they charge no `Quot.sound`. A later module that rewrites a single
entry of a product should cite these rather than the labels. -/

public theorem mul_assoc_apply [CommRing α] (A : Mat m n α) (B : Mat n p α) (C : Mat p q α)
    (i : Fin m) (j : Fin q) : mul (mul A B) C i j = mul A (mul B C) i j := by
  have h : ∀ k : Fin p, CommRing.mul (mul A B i k) (C k j)
      = Vec.sum (fun l => CommRing.mul (A i l) (CommRing.mul (B l k) (C k j))) := by
    intro k
    rw [mul_apply, Vec.sum_mul]
    exact Vec.sum_congr (fun l => CommRing.mul_assoc (A i l) (B l k) (C k j))
  show Vec.sum (fun k => CommRing.mul (mul A B i k) (C k j))
    = Vec.sum (fun l => CommRing.mul (A i l) (mul B C l j))
  rw [Vec.sum_congr h,
    Vec.sum_exchange (fun k l => CommRing.mul (A i l) (CommRing.mul (B l k) (C k j)))]
  exact Vec.sum_congr
    (fun l => (Vec.mul_sum (A i l) (fun k => CommRing.mul (B l k) (C k j))).symm)

public theorem id_mul_apply [CommRing α] (A : Mat m n α) (i : Fin m) (j : Fin n) :
    mul id A i j = A i j := by
  have h : ∀ k : Fin m, CommRing.mul ((id : Mat m m α) i k) (A k j)
      = (if i = k then A k j else AddCommGroup.zero) := by
    intro k
    rw [id_apply]
    refine Decidable.byCases (p := i = k) ?_ ?_
    · intro hk; rw [if_pos hk, if_pos hk, one_mul]
    · intro hk; rw [if_neg hk, if_neg hk, zero_mul]
  show Vec.sum (fun k => CommRing.mul ((id : Mat m m α) i k) (A k j)) = A i j
  rw [Vec.sum_congr h]
  exact Vec.sum_ite_eq i (fun k => A k j)

public theorem mul_id_apply [CommRing α] (A : Mat m n α) (i : Fin m) (j : Fin n) :
    mul A id i j = A i j := by
  have h : ∀ k : Fin n, CommRing.mul (A i k) ((id : Mat n n α) k j)
      = (if k = j then A i k else AddCommGroup.zero) := by
    intro k
    rw [id_apply]
    refine Decidable.byCases (p := k = j) ?_ ?_
    · intro hk; rw [if_pos hk, if_pos hk, mul_one]
    · intro hk; rw [if_neg hk, if_neg hk, mul_zero]
  show Vec.sum (fun k => CommRing.mul (A i k) ((id : Mat n n α) k j)) = A i j
  rw [Vec.sum_congr h]
  exact Vec.sum_ite_eq' j (fun k => A i k)

public theorem map_mul_apply [CommRing α] [CommRing β] (φ : RingHom α β)
    (A : Mat m n α) (B : Mat n p α) (i : Fin m) (j : Fin p) :
    map φ (mul A B) i j = mul (map φ A) (map φ B) i j := by
  show φ.toFun (Vec.sum fun k => CommRing.mul (A i k) (B k j))
    = Vec.sum (fun k => CommRing.mul (φ.toFun (A i k)) (φ.toFun (B k j)))
  rw [hom_map_sum]
  exact Vec.sum_congr (fun k => φ.map_mul (A i k) (B k j))

public theorem apply_neg_apply [CommRing α] (A : Mat m n α) (x : Vec n α) (i : Fin m) :
    apply (neg A) x i = AddCommGroup.neg (apply A x i) := by
  show Vec.sum (fun j => CommRing.mul (AddCommGroup.neg (A i j)) (x j))
    = AddCommGroup.neg (Vec.sum fun j => CommRing.mul (A i j) (x j))
  rw [Vec.sum_congr (fun j => neg_mul (A i j) (x j))]
  exact Vec.sum_neg (fun j => CommRing.mul (A i j) (x j))

end Mat

/-! ## The ring identities of section 19.2

Section 19.1 classifies `M1`-`M4` as `DECIDED` "in the free commutative ring",
holding for **every** morphism at size `O`. They are proved here at every size
by induction on the dimension, which subsumes `O = 8`; nothing below depends
on the parameter layer that fixes `O`.

`M2` and `M3` are the premises of `F1` and `F22` (composition in `AtlLin` is
associative and unital for every morphism, so `R_Q` is a functor); `M1` with
`M2` gives `F3`; `M1`-`M3` together give `F5`, `F17` and `F19a`; `M4` is the
remaining content of `F20` and `T76a`, that the diagonal sign quotient
commutes with the linear action. -/

/-- `M1`. Matrix product entries are integer polynomials in the entries.

Formalised as: entrywise transport along **any** ring homomorphism commutes
with the product.

That is the conclusion `M1` exists to supply. Every use of it -- `F3`, `F5`,
`F17`, `F19a`, `F15a`, `T76a`, `V74` -- reaches it through the ambient lemma
`RH1` of section 19.6, "a ring homomorphism commutes with any
integer-polynomial expression", in order to conclude that extension of scalars
preserves composition. Being a polynomial with integer coefficients is the
premise; commuting with every ring homomorphism is what `RH1` deduces from it,
and it is the only direction the document ever uses. The converse -- that an
entry function natural in the ring must be such a polynomial -- is never
invoked and is not claimed here.

Stating the premise literally would mean building a free commutative ring on
`2 * O^2` indeterminates together with an evaluation map, machinery this
library deliberately does not carry, and would leave the conclusion still to
be derived. `Mat.mul_apply` records the literal shape the document means, a
sum of products of entries with every coefficient `1`, and is true by `rfl`. -/
public theorem M1 [CommRing α] [CommRing β] (φ : RingHom α β)
    (A : Mat m n α) (B : Mat n p α) :
    Mat.map φ (Mat.mul A B) = Mat.mul (Mat.map φ A) (Mat.map φ B) :=
  funext fun i => funext fun j => Mat.map_mul_apply φ A B i j

/-- `M2`. `(AB)C = A(BC)` for all three morphisms. -/
public theorem M2 [CommRing α] (A : Mat m n α) (B : Mat n p α) (C : Mat p q α) :
    Mat.mul (Mat.mul A B) C = Mat.mul A (Mat.mul B C) :=
  funext fun i => funext fun j => Mat.mul_assoc_apply A B C i j

/-- `M3`. Composition is unital for every morphism, on both sides. -/
public theorem M3 [CommRing α] (A : Mat m n α) :
    Mat.mul Mat.id A = A ∧ Mat.mul A Mat.id = A :=
  ⟨funext fun i => funext fun j => Mat.id_mul_apply A i j,
    funext fun i => funext fun j => Mat.mul_id_apply A i j⟩

/-- `M4`. `(-A)x = -(Ax)` for every `A`. -/
public theorem M4 [CommRing α] (A : Mat m n α) (x : Vec n α) :
    Mat.apply (Mat.neg A) x = neg (Mat.apply A x) :=
  funext fun i => Mat.apply_neg_apply A x i

end UorAtlas.Prelude.Linear
