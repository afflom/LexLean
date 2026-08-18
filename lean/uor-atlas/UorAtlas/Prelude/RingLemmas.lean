module
public import Init
public import UorAtlas.Prelude.Algebra
public import UorAtlas.Prelude.Linear
public import UorAtlas.Prelude.NumInstances

/-!
The generic ambient lemmas of section 19.6 of `UOR-ATLAS-FORMAL-001`.

Section 14 reserves the status `DERIVED` for an inference from `PASS` and
`DECIDED` facts *together with named ambient lemmas*, and section 19.6 lists
twelve of those, "used and established nowhere in this document ... these are
the Lean targets". This module discharges the nine that are purely ring- or
field-theoretic and consume no Atlas data: `RH1`, `TI1`, `BC1`, `IG1`, `SD1`,
`QL1`, `DV1`, `LI1`, `FR1`.

Of the remaining three, `FI1` is already proved in
`UorAtlas.Prelude.NumInstances` and is imported here to discharge the
injectivity hypothesis of `TI1`; `RC1` and `RP1` are elsewhere, because each
needs data this module does not have -- a finite group acting on
`Sym^2(RR^O)`, and the restricted product of `D38`.

Everything ring-flavoured is stated over an arbitrary commutative ring rather
than over a constructed `Z_p`. That is not a convenience: it is the route
section 4.4 of the release plan prescribes, "`BC1` through the
ring-parameterized section 13 rather than a constructed `Z_p`". `BC1` below is
therefore base change along an arbitrary `RingHom Int A`, and `SD1` is stated
for a lattice over an arbitrary `A` inside an arbitrary ambient ring receiving
it; instantiating `A := Z_p`, `F := Q_p` recovers the document's `V69` without
this library ever building a completion.
-/

set_option autoImplicit false

namespace UorAtlas.Prelude.RingLemmas

open UorAtlas.Prelude.AddCommGroup
open UorAtlas.Prelude.CommRing
open UorAtlas.Prelude.Linear

universe u v w

/-! ## `RH1`: a ring homomorphism commutes with any integer-polynomial expression

The label quantifies over *expressions*, so the formalization has to quantify
over expressions too. Three readings were available:

* the entrywise matrix identity `Mat.map φ (A * B) = Mat.map φ A * Mat.map φ B`,
  which is `M1` of `UorAtlas.Prelude.Linear` and is the shape the document
  actually applies `RH1` to in `F3`, `F17` and `V74`;
* a normal-form polynomial type (monomials with integer coefficients), which
  would need a normalization theory before `eval` could even be defined;
* the free commutative ring presented by *terms*.

The third is taken. It is the only one of the three that literally says "any
integer-polynomial expression": `IntPoly ν` is the syntax of expressions built
from indeterminates by the ring operations, and `RH1` says `φ` commutes with
the evaluation of every one of them. The other two readings are then recovered
rather than assumed -- `RH1_mul_entry` and `RH1_apply` below derive the matrix
product and matrix action forms from `RH1` by exhibiting the polynomial each
one evaluates, which is what makes the syntactic choice faithful to the use
sites instead of merely adjacent to them.

Integer coefficients need no constructor of their own: `one`, `add` and `neg`
already generate a copy of `Z` inside any commutative ring, so a constructor
carrying an `Int` would buy no expressions and would cost an integer-cast
compatibility lemma. -/

/-- A formal integer-polynomial expression in indeterminates drawn from `ν`. -/
public inductive IntPoly (ν : Type u) where
  | var : ν → IntPoly ν
  | zero : IntPoly ν
  | one : IntPoly ν
  | add : IntPoly ν → IntPoly ν → IntPoly ν
  | neg : IntPoly ν → IntPoly ν
  | mul : IntPoly ν → IntPoly ν → IntPoly ν

namespace IntPoly

/-- Evaluation of an expression at an assignment of ring elements to the
indeterminates. -/
@[expose] public def eval {ν : Type u} {A : Type v} [CommRing A] (x : ν → A) :
    IntPoly ν → A
  | .var t => x t
  | .zero => AddCommGroup.zero
  | .one => CommRing.one
  | .add p q => AddCommGroup.add (eval x p) (eval x q)
  | .neg p => AddCommGroup.neg (eval x p)
  | .mul p q => CommRing.mul (eval x p) (eval x q)

/-- Evaluation depends on the assignment only pointwise. Stated rather than left
to `funext` because every use below is inside a proof that otherwise charges no
axiom at all. -/
public theorem eval_congr {ν : Type u} {A : Type v} [CommRing A] {x y : ν → A}
    (h : ∀ t, x t = y t) (p : IntPoly ν) : eval x p = eval y p := by
  induction p with
  | var t => exact h t
  | zero => rfl
  | one => rfl
  | add p q ihp ihq => show AddCommGroup.add _ _ = AddCommGroup.add _ _; rw [ihp, ihq]
  | neg p ih => show AddCommGroup.neg _ = AddCommGroup.neg _; rw [ih]
  | mul p q ihp ihq => show CommRing.mul _ _ = CommRing.mul _ _; rw [ihp, ihq]

/-- The formal sum of a finite family of expressions. The recursion peels the
first index, matching `Vec.sum`, so `eval_sumPoly` is a three-line induction
instead of an exercise in index arithmetic. -/
@[expose] public def sumPoly {ν : Type u} : {k : Nat} → (Fin k → IntPoly ν) → IntPoly ν
  | 0, _ => .zero
  | _ + 1, f => .add (f 0) (sumPoly fun i => f i.succ)

public theorem eval_sumPoly {ν : Type u} {A : Type v} [CommRing A] (x : ν → A) :
    ∀ {k : Nat} (f : Fin k → IntPoly ν), eval x (sumPoly f) = Vec.sum (fun i => eval x (f i)) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ j ih =>
    intro f
    show AddCommGroup.add (eval x (f 0)) (eval x (sumPoly fun i => f i.succ))
      = AddCommGroup.add (eval x (f 0)) _
    rw [ih (fun i => f i.succ)]

end IntPoly

/-- `RH1` (section 19.6). A ring homomorphism commutes with any
integer-polynomial expression. -/
public theorem RH1 {ν : Type w} {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : RingHom R S) (x : ν → R) (p : IntPoly ν) :
    φ.toFun (IntPoly.eval x p) = IntPoly.eval (fun t => φ.toFun (x t)) p := by
  induction p with
  | var t => rfl
  | zero => exact hom_map_zero φ
  | one => exact φ.map_one
  | add p q ihp ihq =>
    show φ.toFun (AddCommGroup.add _ _) = AddCommGroup.add _ _
    rw [φ.map_add, ihp, ihq]
  | neg p ih =>
    show φ.toFun (AddCommGroup.neg _) = AddCommGroup.neg _
    rw [NumInstances.ringHom_map_neg, ih]
  | mul p q ihp ihq =>
    show φ.toFun (CommRing.mul _ _) = CommRing.mul _ _
    rw [φ.map_mul, ihp, ihq]

/-! ### The two use-site shapes, recovered from `RH1`

`F3`, `F5`, `F17`, `F19a`, `F15a`, `T76a` and `V74` all reach `RH1` in order to
conclude that extension of scalars preserves a matrix product or a matrix
action. Both are evaluations of an explicit `IntPoly`, and both are derived
from `RH1` here rather than reproved, which is the check that the syntactic
statement above really covers the document's uses. -/

/-- The indeterminates of a product of two matrices: one per entry of each
factor. -/
@[expose] public def mulVars {A : Type u} [CommRing A] {m n p : Nat}
    (X : Mat m n A) (Y : Mat n p A) : (Fin m × Fin n) ⊕ (Fin n × Fin p) → A
  | .inl (i, k) => X i k
  | .inr (k, j) => Y k j

/-- The `(i,j)` entry of a matrix product as a formal expression: `M1`'s "sum of
products of entries, every coefficient `1`", written out. -/
@[expose] public def mulEntryPoly (m n p : Nat) (i : Fin m) (j : Fin p) :
    IntPoly ((Fin m × Fin n) ⊕ (Fin n × Fin p)) :=
  IntPoly.sumPoly (fun k : Fin n => .mul (.var (.inl (i, k))) (.var (.inr (k, j))))

public theorem eval_mulEntryPoly {A : Type u} [CommRing A] {m n p : Nat}
    (X : Mat m n A) (Y : Mat n p A) (i : Fin m) (j : Fin p) :
    IntPoly.eval (mulVars X Y) (mulEntryPoly m n p i j) = Mat.mul X Y i j := by
  rw [mulEntryPoly, IntPoly.eval_sumPoly]
  rfl

/-- `RH1` at the matrix product: base change commutes with composition, entry by
entry. This is the form `F3`, `F17` and `F19a` consume. -/
public theorem RH1_mul_entry {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : RingHom R S) {m n p : Nat} (X : Mat m n R) (Y : Mat n p R) (i : Fin m) (j : Fin p) :
    φ.toFun (Mat.mul X Y i j) = Mat.mul (Mat.map φ X) (Mat.map φ Y) i j := by
  rw [← eval_mulEntryPoly X Y i j, RH1, ← eval_mulEntryPoly (Mat.map φ X) (Mat.map φ Y) i j]
  refine IntPoly.eval_congr (fun t => ?_) _
  match t with
  | .inl (a, b) => rfl
  | .inr (a, b) => rfl

/-- `RH1` at the matrix action, which is `V74` and hence `T79`: applying `g` and
then localising is applying `g_v` to the localised vector.

Derived from `RH1_mul_entry` by reading the vector as a one-column matrix, so
the polynomial exhibited for the product serves this case too. -/
public theorem RH1_apply {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : RingHom R S) {m n : Nat} (X : Mat m n R) (x : Vec n R) (i : Fin m) :
    φ.toFun (Mat.apply X x i) = Mat.apply (Mat.map φ X) (Vec.map φ x) i :=
  RH1_mul_entry φ X (fun k (_ : Fin 1) => x k) i 0

/-! ## `TI1`: extension of scalars along a map of fields is injective on coordinates

`M (x)_R S` for `M` free of rank `r` is free of rank `r` over `S` (section 0),
and in the coordinates of a basis the extension is `Vec.map`, one coordinate at
a time. The document's `TI1` hypothesises an *injective* map of fields; no
hypothesis appears below because there is nothing to hypothesise -- `FI1`
already proves every ring homomorphism out of a field into a nonzero ring
injective, and a field is nonzero by `Field.one_ne_zero`. -/

/-- `TI1` (section 19.6). -/
public theorem TI1 {K : Type u} {F : Type v} [Field K] [Field F] (φ : RingHom K F) {n : Nat} :
    Function.Injective (Vec.map φ : Vec n K → Vec n F) := fun _ _ h =>
  funext fun i => NumInstances.FI1 Field.one_ne_zero φ (congrFun h i)

/-! ## `BC1`: an integer matrix with an integer inverse survives base change -/

/-- `G in GL_n(A)`, as the document uses it: a two-sided inverse over `A`.

Membership is an existential rather than a determinant condition on purpose.
Over a general commutative ring the two are equivalent only through the
adjugate, and the adjugate is machinery this module would have to build for no
use: every consumer of `BC1` and `SD1` wants the inverse matrix itself. -/
@[expose] public def InGL {A : Type u} [CommRing A] {n : Nat} (G : Mat n n A) : Prop :=
  ∃ H : Mat n n A, Mat.mul G H = Mat.id ∧ Mat.mul H G = Mat.id

/-- Base change fixes the identity matrix. -/
public theorem map_id {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : RingHom R S) {n : Nat} : Mat.map φ (Mat.id : Mat n n R) = (Mat.id : Mat n n S) := by
  funext i j
  show φ.toFun (if i = j then CommRing.one else AddCommGroup.zero)
    = if i = j then CommRing.one else AddCommGroup.zero
  refine Decidable.byCases (p := i = j) ?_ ?_
  · intro h; rw [if_pos h, if_pos h]; exact φ.map_one
  · intro h; rw [if_neg h, if_neg h]; exact hom_map_zero φ

/-- Invertibility is preserved by base change along any ring homomorphism. -/
public theorem InGL_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : RingHom R S) {n : Nat} {G : Mat n n R} (hG : InGL G) : InGL (Mat.map φ G) := by
  obtain ⟨H, hGH, hHG⟩ := hG
  exact ⟨Mat.map φ H, by rw [← M1, hGH, map_id], by rw [← M1, hHG, map_id]⟩

/-- `BC1` (section 19.6), in the ring-parameterized form section 4.4 of the
release plan asks for: `G in GL_n(Z)` implies `G in GL_n(A)` for every
commutative ring `A` receiving `Z`.

The document writes the conclusion at `Z_p`. Reading it at an arbitrary `A` is
strictly more general and is what lets the place layer be a ring parameter
rather than a construction: `V69` and `V72` cite `BC1` only to move an integral
matrix and its integral inverse into the local ring, and `RingHom Int A` is all
that step ever uses. -/
public theorem BC1 {A : Type u} [CommRing A] (φ : RingHom Int A) {n : Nat}
    {G : Mat n n Int} (hG : InGL G) : InGL (Mat.map φ G) :=
  InGL_map φ hG

/-! ## `IG1`: a group generated by invertible matrices stays invertible

The document's sentence has a premise and a conclusion: "`GL_n(Z)` is closed
under multiplication and inverse, so `V66a` on generators gives
`WLin subset GL_O(Z)`". The premise is `InGL_one`, `InGL_mul` and `InGL_inv`
below; `IG1` is the conclusion, because that is the half a use site consumes --
it has `V66a` for the eight reflections and wants the statement for every
element of the group they generate.

`WLin` is presented by generation (`D41` writes it `< r_a : a in Sim >`), so
the conclusion needs a generated subgroup to quantify over, and `GLGen` is that
subgroup. Three choices in it are worth recording.

* The generators are an indexed family `gens : ι → Mat n n A`, not a list of
  matrices as in `Perm.Gen`. `D41` indexes its generators by the simple roots,
  one reflection per root, so the index is what a use site has in hand; a list
  would demand a membership proof to recover it.
* `one` and `mul` are constructors, matching how a generated matrix group is
  written elsewhere in the library, so a predicate already defined with those
  constructors lands in `GLGen` by a case-per-constructor induction and needs no
  reformulation to reach `IG1`.
* `inv` carries a two-sided inverse as an explicit witness pair rather than
  applying an inverse operation. Over a general commutative ring inversion is a
  relation and not a function: making it a function would need the adjugate,
  which is the machinery `InGL` exists to avoid. The constructor therefore reads
  "a two-sided inverse of a member is a member", which is what the document's
  "closed under inverse" asserts.

Everything is over an arbitrary commutative ring `A`: `A := Int` is the
document's `GL_n(Z)`, and `BC1` moves the conclusion on into any ring receiving
`Z`, which is how `D41`'s `WLin subset GL_Q(V)` follows. -/

/-- The identity is invertible. -/
public theorem InGL_one {A : Type u} [CommRing A] {n : Nat} : InGL (Mat.id : Mat n n A) :=
  ⟨Mat.id, (M3 (Mat.id : Mat n n A)).1, (M3 (Mat.id : Mat n n A)).1⟩

/-- A product of invertible matrices is invertible, with the inverses composed
in the opposite order. -/
public theorem InGL_mul {A : Type u} [CommRing A] {n : Nat} {G K : Mat n n A}
    (hG : InGL G) (hK : InGL K) : InGL (Mat.mul G K) := by
  obtain ⟨H, hGH, hHG⟩ := hG
  obtain ⟨L, hKL, hLK⟩ := hK
  refine ⟨Mat.mul L H, ?_, ?_⟩
  · rw [M2, ← M2 K L H, hKL, (M3 H).1, hGH]
  · rw [M2, ← M2 H G K, hHG, (M3 K).1, hLK]

/-- An inverse of an invertible matrix is invertible: `G` inverts it back. -/
public theorem InGL_inv {A : Type u} [CommRing A] {n : Nat} {G : Mat n n A} (hG : InGL G) :
    ∃ H : Mat n n A, InGL H ∧ Mat.mul G H = Mat.id ∧ Mat.mul H G = Mat.id := by
  obtain ⟨H, hGH, hHG⟩ := hG
  exact ⟨H, ⟨G, hHG, hGH⟩, hGH, hHG⟩

/-- The subgroup of `n x n` matrices over `A` generated by the family `gens`. -/
public inductive GLGen {A : Type u} [CommRing A] {ι : Type w} {n : Nat}
    (gens : ι → Mat n n A) : Mat n n A → Prop
  /-- A generator. -/
  | gen (i : ι) : GLGen gens (gens i)
  /-- The identity. -/
  | one : GLGen gens Mat.id
  /-- Closure under composition. -/
  | mul {G K : Mat n n A} : GLGen gens G → GLGen gens K → GLGen gens (Mat.mul G K)
  /-- Closure under inversion, the inverse supplied as a witness. -/
  | inv {G H : Mat n n A} : GLGen gens G → Mat.mul G H = Mat.id → Mat.mul H G = Mat.id →
      GLGen gens H

/-- `IG1` (section 19.6). Generators in `GL_n(A)` generate a subgroup of
`GL_n(A)`.

The inversion case does not use its inductive hypothesis, and that is the
content of "closed under inverse" rather than a gap: the constructor already
carries the matrix that inverts `H`, so `H` is invertible whatever route put
`G` in the group. -/
public theorem IG1 {A : Type u} [CommRing A] {ι : Type w} {n : Nat} {gens : ι → Mat n n A}
    (hgens : ∀ i, InGL (gens i)) {G : Mat n n A} (hG : GLGen gens G) : InGL G := by
  induction hG with
  | gen i => exact hgens i
  | one => exact InGL_one
  | mul _ _ ihG ihK => exact InGL_mul ihG ihK
  | @inv X H _ hXH hHX _ => exact ⟨X, hHX, hXH⟩

/-! ## `SD1`: a free lattice with unimodular Gram matrix is its own dual

`D31` and `D37` both define a dual by pairing against the lattice and asking
for the answer to be integral: `L* := { y : <y,x> in Z for all x in L }`, and
`L_p* := { y in V_p : <y,x> in Z_p for all x in L_p }`. Both therefore need two
rings, a lattice ring `A` and the ambient ring `F` its span lives in, together
with the structure map `A -> F`. That pair is exactly the data below, and
nothing else about it is used: taking `A := Z_p`, `F := Q_p` gives `V69`
verbatim, and `A := Z`, `F := Q` gives `T58`.

Coordinates are taken with respect to an `A`-basis of the lattice, which the
Atlas has: `V65c` says `Sim` is a `Z`-basis of `L`. So the lattice is the set
of coordinate vectors with entries in the image of `A`, and the form is the one
its Gram matrix defines. -/

section Dual

variable {A : Type u} {F : Type v} [CommRing A] [CommRing F] {n : Nat}

/-- `t` lies in `A`, seen inside the ambient ring: the membership `D37` writes
`<y,x> in Z_p`. -/
@[expose] public def InImage (φ : RingHom A F) (t : F) : Prop := ∃ a : A, t = φ.toFun a

public theorem InImage.zero (φ : RingHom A F) : InImage φ (AddCommGroup.zero : F) :=
  ⟨AddCommGroup.zero, (hom_map_zero φ).symm⟩

public theorem InImage.add {φ : RingHom A F} {s t : F} (hs : InImage φ s) (ht : InImage φ t) :
    InImage φ (AddCommGroup.add s t) := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  exact ⟨AddCommGroup.add a b, by rw [ha, hb, φ.map_add]⟩

public theorem InImage.mul {φ : RingHom A F} {s t : F} (hs : InImage φ s) (ht : InImage φ t) :
    InImage φ (CommRing.mul s t) := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  exact ⟨CommRing.mul a b, by rw [ha, hb, φ.map_mul]⟩

/-- Closure of `A` under the finite sums the form is built from. The induction
consumes the hypothesis one index at a time, so no choice function over the
indices is ever needed. -/
public theorem InImage.sum (φ : RingHom A F) : ∀ {k : Nat} (x : Vec k F),
    (∀ i, InImage φ (x i)) → InImage φ (Vec.sum x) := by
  intro k
  induction k with
  | zero => intro _ _; exact InImage.zero φ
  | succ j ih =>
    intro x h
    rw [Vec.sum_succ]
    exact (h 0).add (ih (fun i => x i.succ) (fun i => h i.succ))

/-- The bilinear form of the lattice, in coordinates: `<c,d> = sum_ij c_i G_ij d_j`. -/
@[expose] public def gramForm (φ : RingHom A F) (Gram : Mat n n A) (c d : Vec n F) : F :=
  Vec.inner c (Mat.apply (Mat.map φ Gram) d)

/-- A coordinate vector is in the lattice exactly when every coordinate is in `A`. -/
@[expose] public def InLattice (φ : RingHom A F) (c : Vec n F) : Prop := ∀ i, InImage φ (c i)

/-- `D31`/`D37`: the dual lattice, pairing integrally against every lattice
vector. -/
@[expose] public def InDual (φ : RingHom A F) (Gram : Mat n n A) (c : Vec n F) : Prop :=
  ∀ d : Vec n F, InLattice φ d → InImage φ (gramForm φ Gram c d)

public theorem map_id_apply (φ : RingHom A F) (i j : Fin n) :
    φ.toFun ((Mat.id : Mat n n A) i j) = (Mat.id : Mat n n F) i j :=
  congrFun (congrFun (map_id φ) i) j

/-- The image of the `j`-th basis vector of the lattice. -/
@[expose] public def basisVec (φ : RingHom A F) (j : Fin n) : Vec n F :=
  fun i => φ.toFun ((Mat.id : Mat n n A) i j)

public theorem inLattice_basisVec (φ : RingHom A F) (j : Fin n) :
    InLattice φ (basisVec φ j) := fun i => ⟨(Mat.id : Mat n n A) i j, rfl⟩

public theorem gramForm_basisVec (φ : RingHom A F) (Gram : Mat n n A) (c : Vec n F) (j : Fin n) :
    gramForm φ Gram c (basisVec φ j)
      = Vec.sum (fun i => CommRing.mul (c i) (Mat.map φ Gram i j)) := by
  refine Vec.sum_congr (fun i => congrArg (CommRing.mul (c i)) ?_)
  show Vec.sum (fun l => CommRing.mul (Mat.map φ Gram i l) (basisVec φ j l))
    = Mat.map φ Gram i j
  refine Eq.trans (Vec.sum_congr
    (y := fun l => CommRing.mul (Mat.map φ Gram i l) ((Mat.id : Mat n n F) l j))
    (fun l => congrArg (CommRing.mul (Mat.map φ Gram i l)) (map_id_apply φ l j))) ?_
  exact Mat.mul_id_apply (Mat.map φ Gram) i j

/-- Every lattice vector is in the dual: the Gram entries are in `A` by
construction, so no invertibility is involved in this half. -/
public theorem inDual_of_inLattice (φ : RingHom A F) (Gram : Mat n n A) {c : Vec n F}
    (hc : InLattice φ c) : InDual φ Gram c := by
  intro d hd
  refine InImage.sum φ _ (fun i => (hc i).mul ?_)
  exact InImage.sum φ _ (fun j => InImage.mul ⟨Gram i j, rfl⟩ (hd j))

/-- The converse, and the whole content of `SD1`: an inverse Gram matrix over
`A` turns integrality of the pairings against the basis back into integrality of
the coordinates. -/
public theorem inLattice_of_inDual (φ : RingHom A F) {Gram : Mat n n A} (hG : InGL Gram)
    {c : Vec n F} (hc : InDual φ Gram c) : InLattice φ c := by
  obtain ⟨H, hGH, _⟩ := hG
  intro k
  have key : Vec.sum (fun j => CommRing.mul (gramForm φ Gram c (basisVec φ j))
      (Mat.map φ H j k)) = c k := by
    have hsum : ∀ j : Fin n, CommRing.mul (gramForm φ Gram c (basisVec φ j)) (Mat.map φ H j k)
        = Vec.sum (fun i => CommRing.mul (c i)
            (CommRing.mul (Mat.map φ Gram i j) (Mat.map φ H j k))) := by
      intro j
      rw [gramForm_basisVec, Vec.sum_mul]
      exact Vec.sum_congr (fun i =>
        CommRing.mul_assoc (c i) (Mat.map φ Gram i j) (Mat.map φ H j k))
    rw [Vec.sum_congr hsum, Vec.sum_exchange (fun j i => CommRing.mul (c i)
      (CommRing.mul (Mat.map φ Gram i j) (Mat.map φ H j k)))]
    have hrow : ∀ i : Fin n, Vec.sum (fun j => CommRing.mul (c i)
        (CommRing.mul (Mat.map φ Gram i j) (Mat.map φ H j k)))
        = CommRing.mul (c i) ((Mat.id : Mat n n F) i k) := by
      intro i
      rw [← Vec.mul_sum]
      refine congrArg (CommRing.mul (c i)) ?_
      show Mat.mul (Mat.map φ Gram) (Mat.map φ H) i k = (Mat.id : Mat n n F) i k
      rw [← M1, hGH]
      exact map_id_apply φ i k
    rw [Vec.sum_congr hrow]
    exact Mat.mul_id_apply (m := 1) (fun _ => c) 0 k
  refine key ▸ InImage.sum φ _ (fun j => InImage.mul ?_ ⟨H j k, rfl⟩)
  exact hc (basisVec φ j) (inLattice_basisVec φ j)

/-- `SD1` (section 19.6). For a commutative ring `A`, a free `A`-lattice whose
Gram matrix lies in `GL_n(A)` equals its dual.

Set equality is stated as the extensional biconditional rather than as an
equality of subtypes, because both `D31` and `D37` are set-builder
descriptions and every use of them -- `T58`, `T67`, `V69` -- is a membership
transfer. -/
public theorem SD1 (φ : RingHom A F) {Gram : Mat n n A} (hG : InGL Gram) (c : Vec n F) :
    InDual φ Gram c ↔ InLattice φ c :=
  ⟨fun h => inLattice_of_inDual φ hG h, fun h => inDual_of_inLattice φ Gram h⟩

end Dual

/-! ## `QL1`: a diagonal group quotient is well defined on an equivariant map

`D44` quotients `Addr(L)` by "a single global sign, not one per place", and
`D45` defines `Delta_K` on `K = R/{+1,-1}` by choosing a representative root.
The lemma those two need is that one group acting on both sides -- the
*diagonal* -- descends an equivariant map to the orbit sets.

No group axioms appear below, and that is deliberate rather than an omission:
well-definedness needs only that the same element `g` acts on source and
target, so imposing a `Group` class the prelude does not have would add a
hypothesis no use site can supply more cheaply. -/

/-- The orbit relation of an action `act` of `G` on `X`. -/
@[expose] public def OrbitRel {G : Type u} {X : Type v} (act : G → X → X) (x y : X) : Prop :=
  ∃ g : G, act g x = y

/-- `QL1` (section 19.6). -/
public theorem QL1 {G : Type u} {X : Type v} {Y : Type w}
    (act : G → X → X) (bct : G → Y → Y) (f : X → Y)
    (hf : ∀ (g : G) (x : X), f (act g x) = bct g (f x))
    {x y : X} (h : OrbitRel act x y) : OrbitRel bct (f x) (f y) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, by rw [← hg, hf g x]⟩

/-- The induced map on orbit sets, which is what "well defined" is *for*:
`Delta_K` of `D45` is this map for the diagonal sign action. -/
@[expose] public def QL1.descend {G : Type u} {X : Type v} {Y : Type w}
    (act : G → X → X) (bct : G → Y → Y) (f : X → Y)
    (hf : ∀ (g : G) (x : X), f (act g x) = bct g (f x)) :
    Quot (OrbitRel act) → Quot (OrbitRel bct) :=
  Quot.lift (fun x => Quot.mk _ (f x)) (fun _ _ h => Quot.sound (QL1 act bct f hf h))

public theorem QL1.descend_mk {G : Type u} {X : Type v} {Y : Type w}
    (act : G → X → X) (bct : G → Y → Y) (f : X → Y)
    (hf : ∀ (g : G) (x : X), f (act g x) = bct g (f x)) (x : X) :
    QL1.descend act bct f hf (Quot.mk _ x) = Quot.mk _ (f x) := rfl

/-- The diagonal sign action of `{+1,-1}` on an additive group: `D12`'s
`K = R/{+1,-1}` and `D44`'s `PAddr(L) = Addr(L)/{+1,-1}_diag` are its orbit
sets. `Bool` indexes the two signs because the prelude has no two-element
group and `QL1` needs none. -/
@[expose] public def signAct {X : Type u} [AddCommGroup X] : Bool → X → X
  | true, x => AddCommGroup.neg x
  | false, x => x

/-- `QL1` at the diagonal sign quotient, the instance `T80a` and `F20` cite. The
equivariance hypothesis is exactly `M4`'s `(-A)x = -(Ax)`, which is why those
entries name `QL1` and `RP1` together. -/
public theorem QL1_sign {X : Type u} {Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (f : X → Y) (hf : ∀ x, f (AddCommGroup.neg x) = AddCommGroup.neg (f x))
    {x y : X} (h : OrbitRel signAct x y) : OrbitRel signAct (f x) (f y) :=
  QL1 signAct signAct f (fun g x => by cases g with
    | true => exact hf x
    | false => rfl) h

/-! ## `DV1`: a nonzero integer has finitely many prime divisors

`V70` needs this for "the bad-denominator set", the finitely many places at
which a fixed rational family can fail to be integral. Section 19.1 is emphatic
that `L1` and `L2` -- the `SMT-VALIDATED` bounds on prime divisors -- are
"non-normative validation evidence only" and "no derivation may take them as a
premise", so the bound below is proved rather than cited.

Finiteness is stated as containment in an explicit list. That is the only
notion of finite subset available without `Finset`, and it is the one `V70`
actually consumes: it enumerates the exceptional places. -/

/-- Section 0's `Prime`. -/
@[expose] public def IsPrime (p : Nat) : Prop := 1 < p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- A predicate on `Nat` is finite when a single list contains everything
satisfying it. -/
@[expose] public def IsFinite (P : Nat → Prop) : Prop := ∃ l : List Nat, ∀ p : Nat, P p → p ∈ l

/-- `DV1` (section 19.6). If `m != 0` then `{ p in Prime : p divides m }` is
finite.

Primality is carried in the statement because the document's set is a set of
primes, and it is unused in the proof because dropping it only enlarges the
set: every divisor of a nonzero `m` is bounded by `|m|`. -/
public theorem DV1 {m : Int} (hm : m ≠ 0) : IsFinite (fun p => IsPrime p ∧ (p : Int) ∣ m) := by
  refine ⟨List.range (m.natAbs + 1), fun p hp => List.mem_range.mpr ?_⟩
  have hpos : 0 < m.natAbs := Nat.pos_of_ne_zero (fun h => hm (Int.natAbs_eq_zero.mp h))
  have hdvd : p ∣ m.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hp.2
    rwa [Int.natAbs_natCast] at h
  exact Nat.lt_succ_of_le (Nat.le_of_dvd hpos hdvd)

/-! ## `FR1` and `LI1`: finite denominators, and integrality away from them

`D34` makes `V = L (x)_Z Q` the single rational carrier, and `V65c` makes `Sim`
a `Z`-basis of `L`, so in those coordinates `L` is `Z^n` and `V` is `Q^n`.
`FR1` is then the statement that a rational vector has a common denominator,
and `LI1` that clearing it leaves the result integral at every prime that
misses it. Together they are what `V70` runs on. -/

/-- Clearing one rational's denominator. Core `Rat` keeps its numerator and
denominator reduced, which is what makes `LI1` below have content: the
denominator that `LI1` tests against `p` is the reduced one, not whichever
denominator happened to be written down. -/
public theorem den_mul_eq_num (q : Rat) : ((q.den : Int) : Rat) * q = (q.num : Rat) := by
  have hd : ((q.den : Int) : Rat) ≠ 0 := by
    rw [Ne, Rat.intCast_eq_zero_iff]
    have h := q.den_nz
    omega
  have key : (q.num : Rat) / ((q.den : Int) : Rat) = q := by
    rw [← Rat.divInt_eq_div]
    exact Rat.num_divInt_den q
  calc ((q.den : Int) : Rat) * q
      = ((q.den : Int) : Rat) * ((q.num : Rat) / ((q.den : Int) : Rat)) := by rw [key]
    _ = (q.num : Rat) / ((q.den : Int) : Rat) * ((q.den : Int) : Rat) := Rat.mul_comm _ _
    _ = (q.num : Rat) := Rat.div_mul_cancel hd

/-- `FR1` in the multiplicative form the induction produces. Kept public
because it, rather than the quotient form, is what chains into `LI1`. -/
public theorem exists_common_denominator : ∀ {n : Nat} (x : Vec n Rat),
    ∃ (y : Vec n Int) (m : Int), 0 < m ∧ ∀ i, (m : Rat) * x i = (y i : Rat) := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨fun i => i.elim0, 1, by decide, fun i => i.elim0⟩
  | succ k ih =>
    intro x
    obtain ⟨y', m', hm', h'⟩ := ih (fun i => x i.succ)
    refine ⟨Fin.cases (m' * (x 0).num) (fun i => ((x 0).den : Int) * y' i),
      ((x 0).den : Int) * m', Int.mul_pos ?_ hm', ?_⟩
    · have h := (x 0).den_pos
      omega
    · refine Fin.cases ?_ ?_
      · show ((((x 0).den : Int) * m' : Int) : Rat) * x 0 = ((m' * (x 0).num : Int) : Rat)
        rw [Rat.intCast_mul, Rat.intCast_mul, Rat.mul_comm (((x 0).den : Int) : Rat) _,
          Rat.mul_assoc, den_mul_eq_num]
      · intro i
        show ((((x 0).den : Int) * m' : Int) : Rat) * x i.succ
          = ((((x 0).den : Int) * y' i : Int) : Rat)
        rw [Rat.intCast_mul, Rat.intCast_mul, Rat.mul_assoc, h' i]

/-- `FR1` (section 19.6). Every element of `L (x)_Z Q` has a finite-denominator
form `y/m` with `y in L` and `m > 0`. -/
public theorem FR1 {n : Nat} (x : Vec n Rat) :
    ∃ (y : Vec n Int) (m : Int), 0 < m ∧ ∀ i, x i = (y i : Rat) / (m : Rat) := by
  obtain ⟨y, m, hm, h⟩ := exists_common_denominator x
  have hm0 : (m : Rat) ≠ 0 := by
    rw [Ne, Rat.intCast_eq_zero_iff]
    omega
  refine ⟨y, m, hm, fun i => ?_⟩
  rw [← h i, Rat.mul_comm, Rat.mul_div_cancel hm0]

/-- `x` is integral at `p`: `p` misses the reduced denominator. This is
membership in the localization `Z_(p)`, and hence in `Z_p` after completion,
without either ring being constructed. -/
@[expose] public def IntegralAt (p : Nat) (x : Rat) : Prop := ¬ (p ∣ x.den)

/-- Writing `x` with denominator `m` bounds its reduced denominator by `m`. -/
public theorem den_dvd_of_scale {x : Rat} {y m : Int} (h : (m : Rat) * x = (y : Rat)) :
    x.den ∣ m.natAbs := by
  have key : ((m * x.num : Int) : Rat) = (((x.den : Int) * y : Int) : Rat) := by
    rw [Rat.intCast_mul, Rat.intCast_mul, ← den_mul_eq_num x, ← Rat.mul_assoc,
      Rat.mul_comm (m : Rat) _, Rat.mul_assoc, h]
  have hint : (x.den : Int) ∣ m * x.num := ⟨y, Rat.intCast_inj.mp key⟩
  have hnat : x.den ∣ m.natAbs * x.num.natAbs := by
    have h2 := Int.natAbs_dvd_natAbs.mpr hint
    rwa [Int.natAbs_natCast, Int.natAbs_mul] at h2
  exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm x.reduced) hnat

/-- `LI1` (section 19.6). `x = y/m` with `m != 0` is integral at every `p` not
dividing `m`.

Primality of `p` is not required and is therefore not assumed; the document
applies this only at primes, and the unrestricted statement is what `V70`
needs, since it must range over the complement of the finite set `DV1`
bounds. -/
public theorem LI1 {p : Nat} {x : Rat} {y m : Int} (hm : m ≠ 0)
    (hx : x = (y : Rat) / (m : Rat)) (hp : ¬ ((p : Int) ∣ m)) :
    IntegralAt p x := by
  have hm0 : (m : Rat) ≠ 0 := by
    rw [Ne, Rat.intCast_eq_zero_iff]
    exact hm
  have hscale : (m : Rat) * x = (y : Rat) := by
    rw [hx, Rat.mul_comm, Rat.div_mul_cancel hm0]
  intro hdvd
  refine hp ?_
  have h1 : p ∣ m.natAbs := Nat.dvd_trans hdvd (den_dvd_of_scale hscale)
  have h2 : ((p : Nat) : Int).natAbs ∣ m.natAbs := by rwa [Int.natAbs_natCast]
  exact Int.natAbs_dvd_natAbs.mp h2

end UorAtlas.Prelude.RingLemmas
