module
public import Init
public import UorAtlas.Prelude.Algebra
public import UorAtlas.Prelude.Linear
public import UorAtlas.Prelude.NumInstances
public import UorAtlas.Prelude.RingLemmas
public import UorAtlas.Roots
public import UorAtlas.Category

/-!
Section 18 of `UOR-ATLAS-FORMAL-001`: **localisation as a functor**.

The section exists to make one thing machine-checkable. An earlier formulation
asserted a natural transformation between `Id : AtlLin -> AtlLin` and a
`Loc_v : AtlLin -> AtlLin_v` whose codomain was undefined; `F8`-`F11` were
retracted for that reason (section 20.1), and `D64` replaces the prose with a
*signature table* "so that ill-typed naturality cannot be asserted". `F12`
records the retraction and says what the fix is: "the signature table of `D65`
makes this a machine check rather than a reading."

This module is that machine check. `NatTrans` below is indexed by **one** pair
of categories, so writing `loc_v : R_Q => R_v` at all forces `R_Q` and `R_v` to
share source *and* target; `Across` and `F12` state the law that makes the
withdrawn pairing unwritable, and `D64.Signature` is the table itself as a
record whose five field types are the five rows.

The document's order is followed exactly, and it says why: "Construction
precedes typing. `F22`, `F17`, `F19a` and `F15a` establish that `R_Q`, `R_v`,
`R_Addr` and `Pf` are functors; only then do `F13`-`F15` assert that `loc_v`,
`Delta` and `Delta_K` have natural-transformation types." So `D65` gives the
object and morphism *assignments*, the four functoriality theorems are proved
about those assignments, and only afterwards are the five `CatFunctor` records
bundled and the table inhabited.

## No real numbers, and no constructed completions

`Qv(arch) = RR` and `Qv(finite(p)) = Q_p`, and this library builds neither.
Nothing in section 18 needs them built. Section 19.3 is explicit that the only
property of `Qv(v)` any derivation uses is that it is a **nonzero commutative
ring receiving a ring homomorphism from `Q`** -- that is exactly the hypothesis
`A1` carries -- and section 19.6 discharges the rest through ambient lemmas
that `UorAtlas.Prelude.RingLemmas` proves over an arbitrary commutative ring.
`QAlg` below is therefore that interface, and `LocData.Qv` is a family of them.
Instantiating `Qv v := Q_p` and `Adr :=` the ring of adeles recovers the
document's statements verbatim without this module ever mentioning a
completion, which is the same route section 4.4 of the release plan prescribes
for `BC1`.

The one place where this is a genuine loss is recorded in `D62` below:
`component_dims`, the eigenspace dimensions of a generic commutant element, is
not formalised, because eigenvalue multiplicities are not expressible over `Z`
or `Q` without the spectral machinery of section 16. `lift_linear`,
`sym2_rep` and `commutant` are formalised, exactly and over `Q`.

## What this module is parameterised over

`LocData` is the section-18 analogue of `UorAtlas.Category.ActionData`: one
record carrying the places, the address ring, `WLin`, `Aut`, `pi`, a lift, and
the class set with its `Aut` action. Every theorem below is stated for such a
record, and `TwoPlace.witness` at the end **exhibits one**, so nothing here is
true of nothing. The witness takes `WLin = {+I,-I}` -- `V68b`'s `-I in WLin` --
over two places with `Addr := Q x Q` and `Delta` the diagonal, which is the
smallest instance in which `T76a` has content: `I` and `-I` are two different
lifts of the same automorphism, and the theorem is that they induce the same
map on `PAddr(L)`.

## Section-13 data defined here, for the integrator

`UorAtlas.Places` is being written concurrently and owns `D33`-`D51` and the
restricted product. It was not importable when this module was written, so the
three section-13 constructions section 18 consumes are defined here, in the
block marked "Section-13 data" below, and **only** those three:

* `D44`, `PAddr(L) := Addr(L)/{+1,-1}_diag`, as the orbit set of
  `RingLemmas.signAct`;
* `D45`, `Delta_K`, at a chosen class representative;
* `D46`, `tau_Addr`, at the chosen lift `LocData.lift`.

`Addr(L)` itself is *not* redefined: `LocData.Adr` is the coordinate ring of
`D38`'s restricted product together with its place projections, which is the
whole of what `D39`, `F7`, `F19` and `RP1` use it for. When `UorAtlas.Places`
lands, its restricted product supplies `LocData.Adr` and these three
definitions should be merged into it rather than duplicated.

## Labels of the place layer that are *not* claimed here

`T77a` and `T78`-`T83` lie in section 13's theorem list, which
`UorAtlas.Places` is tasked with. `F6` and `F16` are section 18's own
statements of the naturality square that section 13 labels `T79`, and `F20`'s
naturality equation is section 13's `T80`; those squares are proved here under
their section-18 labels, and the `T` names are left to the module that owns
the section they are stated in. `T76a` **is** claimed here: it carries a bold
entry in section 18 and sits in section 18's block of the label register.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace UorAtlas.Functor

open UorAtlas.Prelude
open UorAtlas.Prelude.AddCommGroup
open UorAtlas.Prelude.CommRing
open UorAtlas.Prelude.Linear
open UorAtlas.Category

/-! ## Linear algebra the section needs and the prelude does not carry

`UorAtlas.Prelude.Linear` proves `M1`-`M4` and the entrywise cores of the
matrix laws. Five consequences are used repeatedly below and are collected
here so that no proof of a labelled statement has to re-derive them. Each is
`M2`, `M3` or `M4` read at a one-column matrix, which is why none of them
needs an induction of its own. -/

/-- The identity matrix acts as the identity. `M3` at a one-column matrix. -/
public theorem apply_id {α : Type} [CommRing α] {n : Nat} (x : Vec n α) :
    Mat.apply (Mat.id : Mat n n α) x = x := by
  funext i
  have h : ∀ j : Fin n, CommRing.mul ((Mat.id : Mat n n α) i j) (x j)
      = (if i = j then x j else AddCommGroup.zero) := by
    intro j
    rw [Mat.id_apply]
    refine Decidable.byCases (p := i = j) ?_ ?_
    · intro hj; rw [if_pos hj, if_pos hj, CommRing.one_mul]
    · intro hj; rw [if_neg hj, if_neg hj, zero_mul]
  show Vec.sum (fun j => CommRing.mul ((Mat.id : Mat n n α) i j) (x j)) = x i
  rw [Vec.sum_congr h]
  exact Vec.sum_ite_eq i x

/-- Composition of matrices is composition of the maps they define. `M2` at a
one-column matrix, which is how `F5`, `F17`, `F19a` and `F15a` all reach it. -/
public theorem apply_mul {α : Type} [CommRing α] {m n p : Nat}
    (A : Mat m n α) (B : Mat n p α) (x : Vec p α) :
    Mat.apply (Mat.mul A B) x = Mat.apply A (Mat.apply B x) :=
  funext fun i => Mat.mul_assoc_apply A B (fun k (_ : Fin 1) => x k) i 0

/-- The matrix action is additive. -/
public theorem apply_add {α : Type} [CommRing α] {m n : Nat} (A : Mat m n α) (x y : Vec n α) :
    Mat.apply A (AddCommGroup.add x y)
      = AddCommGroup.add (Mat.apply A x) (Mat.apply A y) := by
  funext i
  show Vec.sum (fun j => CommRing.mul (A i j) (AddCommGroup.add (x j) (y j)))
    = AddCommGroup.add (Vec.sum fun j => CommRing.mul (A i j) (x j))
        (Vec.sum fun j => CommRing.mul (A i j) (y j))
  rw [Vec.sum_congr (fun j => CommRing.left_distrib (A i j) (x j) (y j))]
  exact Vec.sum_add _ _

/-- The matrix action commutes with scalars: this is what makes every `R_v(g)`
below a morphism of `Q`-modules rather than merely a map of sets. -/
public theorem apply_smul {α : Type} [CommRing α] {m n : Nat} (A : Mat m n α) (c : α)
    (x : Vec n α) : Mat.apply A (Vec.smul c x) = Vec.smul c (Mat.apply A x) := by
  funext i
  show Vec.sum (fun j => CommRing.mul (A i j) (CommRing.mul c (x j)))
    = CommRing.mul c (Vec.sum fun j => CommRing.mul (A i j) (x j))
  rw [Vec.mul_sum]
  exact Vec.sum_congr (fun j => by
    rw [← CommRing.mul_assoc, ← CommRing.mul_assoc, CommRing.mul_comm (A i j) c])

/-- `M4` with the sign on the vector rather than on the matrix. `QL1_sign`
takes its equivariance hypothesis in this form, and `T76a`, `F15a` and `F20`
are the three places that supply it. -/
public theorem apply_neg {α : Type} [CommRing α] {m n : Nat} (A : Mat m n α) (x : Vec n α) :
    Mat.apply A (AddCommGroup.neg x) = AddCommGroup.neg (Mat.apply A x) := by
  rw [← M4 A x]
  funext i
  refine Vec.sum_congr (fun j => ?_)
  show CommRing.mul (A i j) (AddCommGroup.neg (x j))
    = CommRing.mul (AddCommGroup.neg (A i j)) (x j)
  rw [Linear.neg_mul, CommRing.mul_comm (A i j) (AddCommGroup.neg (x j)), Linear.neg_mul,
    CommRing.mul_comm (x j) (A i j)]

/-- Double negation, needed wherever the diagonal sign quotient is unwound. -/
public theorem neg_neg {α : Type} [AddCommGroup α] (a : α) :
    AddCommGroup.neg (AddCommGroup.neg a) = a := by
  refine Prelude.add_left_cancel (a := AddCommGroup.neg a) ?_
  rw [AddCommGroup.add_neg, neg_add_cancel]

/-- Base change is compatible with negation, entrywise on a matrix. -/
public theorem map_neg_mat {A B : Type} [CommRing A] [CommRing B] (φ : RingHom A B)
    {m n : Nat} (M : Mat m n A) :
    Mat.map φ (Mat.neg M) = Mat.neg (Mat.map φ M) :=
  funext fun i => funext fun j => NumInstances.ringHom_map_neg φ (M i j)

/-- Base change is compatible with negation, entrywise on a vector. -/
public theorem map_neg_vec {A B : Type} [CommRing A] [CommRing B] (φ : RingHom A B)
    {n : Nat} (x : Vec n A) :
    Vec.map φ (AddCommGroup.neg x) = AddCommGroup.neg (Vec.map φ x) :=
  funext fun i => NumInstances.ringHom_map_neg φ (x i)

/-- Base change commutes with the matrix action. This is `RH1_apply` of
section 19.6 with the `funext` taken, and it is the single fact behind `F6`,
`F16`, `F18`, `F19` and `F20`. -/
public theorem map_apply {A B : Type} [CommRing A] [CommRing B] (φ : RingHom A B)
    {m n : Nat} (M : Mat m n A) (x : Vec n A) :
    Vec.map φ (Mat.apply M x) = Mat.apply (Mat.map φ M) (Vec.map φ x) :=
  funext fun i => RingLemmas.RH1_apply φ M x i

/-! ## Natural transformations and functor categories

`UorAtlas.Category` gives `Cat` and `CatFunctor`; it has no natural
transformations, because sections 7 and 9 needed none. Section 18 needs them,
and needs the functor category `[B WLin, QMod]` that `D66`'s `LocalRep` maps
into.

The indexing is the point. `NatTrans` takes `F G : CatFunctor C D` for **one**
`C` and **one** `D`. That is not a convenience of presentation: it is the
typing law whose violation retracted `F8`-`F11`, and `F12` below states it. -/

/-- A natural transformation. Its two functors share source **and** target by
construction. -/
public structure NatTrans {C D : Cat} (F G : CatFunctor C D) where
  /-- The component at each object. -/
  app : (X : C.Ob) → D.Hom (F.obj X) (G.obj X)
  /-- The naturality square. -/
  naturality : ∀ {X Y : C.Ob} (f : C.Hom X Y),
    D.comp (app Y) (F.map f) = D.comp (G.map f) (app X)

/-- Two natural transformations with equal components are equal: the naturality
field is a `Prop` and so carries no data. -/
public theorem NatTrans.ext {C D : Cat} {F G : CatFunctor C D} {η θ : NatTrans F G}
    (h : ∀ X, η.app X = θ.app X) : η = θ := by
  obtain ⟨a, _⟩ := η
  obtain ⟨b, _⟩ := θ
  have hab : a = b := funext h
  subst hab
  rfl

/-- The identity natural transformation. -/
@[expose] public def NatTrans.idt {C D : Cat} (F : CatFunctor C D) : NatTrans F F where
  app X := D.idm (F.obj X)
  naturality f := by rw [D.id_comp, D.comp_id]

/-- Vertical composition. -/
@[expose] public def NatTrans.vcomp {C D : Cat} {F G H : CatFunctor C D}
    (η : NatTrans G H) (θ : NatTrans F G) : NatTrans F H where
  app X := D.comp (η.app X) (θ.app X)
  naturality f := by
    rw [D.assoc, θ.naturality f, ← D.assoc, η.naturality f, D.assoc]

/-- `[C, D]`, the functor category. `D66`'s `LocalRep` lands in this. -/
@[expose] public def funCat (C D : Cat) : Cat where
  Ob := CatFunctor C D
  Hom F G := NatTrans F G
  idm F := NatTrans.idt F
  comp η θ := NatTrans.vcomp η θ
  id_comp η := NatTrans.ext fun X => D.id_comp (η.app X)
  comp_id η := NatTrans.ext fun X => D.comp_id (η.app X)
  assoc h g f := NatTrans.ext fun X => D.assoc (h.app X) (g.app X) (f.app X)

/-- The component family of a would-be natural transformation, without the
naturality square. `F13`-`F15` are exactly assertions that a family of this
type can be written down, which is what "well typed" means for them; `F16`,
`F18`, `F19` and `F20` then supply the squares. -/
@[expose] public def ComponentFamily {C D : Cat} (F G : CatFunctor C D) : Type :=
  (X : C.Ob) → D.Hom (F.obj X) (G.obj X)

/-! ## Groups, and subgroups of `GL_n(Q)`

`D41` puts `WLin` inside `GL_Q(V)`, and `D63` makes its elements the morphisms
of `AtlLin`. A subgroup is presented by a membership predicate together with a
chosen inverse, rather than by a determinant condition: over `Q` the two agree,
but every consumer below -- `F5`, `T76a`, `F15a` -- wants the inverse matrix
itself, which is the same reason `RingLemmas.InGL` is an existential. -/

/-- A group, as `D64`'s `B G` needs one. -/
public structure GrpData where
  /-- The underlying set. -/
  El : Type
  /-- The unit. -/
  one : El
  /-- The product. -/
  mul : El → El → El
  /-- The inverse. -/
  inv : El → El
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  inv_mul : ∀ a, mul (inv a) a = one
  mul_inv : ∀ a, mul a (inv a) = one

/-- The unit of a group is the only idempotent solution of `a a = a`. Used to
derive `pi(1) = 1` rather than assume it. -/
public theorem GrpData.eq_one_of_self_mul (G : GrpData) {a : G.El} (h : G.mul a a = a) :
    a = G.one := by
  have h1 : G.mul (G.inv a) (G.mul a a) = G.mul (G.inv a) a := by rw [h]
  rw [← G.mul_assoc, G.inv_mul, G.one_mul] at h1
  exact h1

/-- A subgroup of `GL_n(Q)`: `D41`'s `WLin`. -/
public structure MatGroup (n : Nat) where
  /-- Membership. -/
  Mem : Mat n n Rat → Prop
  id_mem : Mem Mat.id
  mul_mem : ∀ {A B : Mat n n Rat}, Mem A → Mem B → Mem (Mat.mul A B)
  /-- The inverse of a member, which `F5` needs as a matrix and not only as an
  existential. -/
  invOf : (A : Mat n n Rat) → Mem A → Mat n n Rat
  invOf_mem : ∀ {A : Mat n n Rat} (h : Mem A), Mem (invOf A h)
  mul_invOf : ∀ {A : Mat n n Rat} (h : Mem A), Mat.mul A (invOf A h) = Mat.id
  invOf_mul : ∀ {A : Mat n n Rat} (h : Mem A), Mat.mul (invOf A h) A = Mat.id

/-- An element of `WLin`. -/
public abbrev MatGroup.El {n : Nat} (W : MatGroup n) : Type := { A : Mat n n Rat // W.Mem A }

/-- `WLin` as an abstract group. The five laws are `M2`, `M3` and the two
inverse equations, which is precisely the content `F1` records. -/
@[expose] public def MatGroup.grp {n : Nat} (W : MatGroup n) : GrpData where
  El := W.El
  one := ⟨Mat.id, W.id_mem⟩
  mul a b := ⟨Mat.mul a.val b.val, W.mul_mem a.property b.property⟩
  inv a := ⟨W.invOf a.val a.property, W.invOf_mem a.property⟩
  one_mul a := Subtype.ext (M3 a.val).1
  mul_one a := Subtype.ext (M3 a.val).2
  mul_assoc a b c := Subtype.ext (M2 a.val b.val c.val)
  inv_mul a := Subtype.ext (W.invOf_mul a.property)
  mul_inv a := Subtype.ext (W.mul_invOf a.property)

/-! ## `Qv(v)` as an interface

Section 19.3: the only thing any derivation uses about a completion is that it
is a nonzero commutative ring receiving `iota_v : Q -> Qv(v)`. That is this
record, and `A1` is available at it verbatim. -/

/-- A commutative `Q`-algebra: `Qv(v)` of `D33`, and the coordinate ring of
`D38`'s restricted product, presented by the only properties section 18 uses. -/
public structure QAlg where
  /-- The carrier. -/
  Car : Type
  [ring : CommRing Car]
  /-- `iota_v : Q -> Qv(v)`, section 0. -/
  str : RingHom Rat Car
  /-- Nonzero, which is what `A1` needs and all it needs. -/
  one_ne_zero : (CommRing.one : Car) ≠ AddCommGroup.zero

public instance instQAlgRing (A : QAlg) : CommRing A.Car := A.ring

/-- `A1` at a `QAlg`: every structure map is injective. Section 19.3 insists
this is derived, and `UorAtlas.Prelude.NumInstances.A1` is that derivation. -/
public theorem QAlg.str_injective (A : QAlg) : Function.Injective A.str.toFun :=
  NumInstances.A1 A.one_ne_zero A.str

/-- `Q` itself, the `QAlg` the rational carrier `V` of `D34` is free over. -/
@[expose] public def QAlg.rat : QAlg where
  Car := Rat
  str := { toFun := fun q => q, map_one := rfl, map_add := fun _ _ => rfl,
           map_mul := fun _ _ => rfl }
  one_ne_zero := by decide


/-! ## What section 18 runs over

`LocData` is to this module what `ActionData` is to `UorAtlas.Category`: the
data every statement below is quantified over, and the thing
`TwoPlace.witness` exhibits.

Three choices in it are worth the ink.

* `Adr` is a `QAlg`, not a construction. `D38`'s `Addr(L)` is a restricted
  product, and `RP1` says the only structure any derivation takes from it is
  that it carries a `Q`-module structure closed under the operations and that
  `Delta` is `Q`-linear. In the coordinates of `V65c`'s `Z`-basis that is
  exactly "a commutative ring receiving `Q`", with the place components as
  ring homomorphisms out of it. `UorAtlas.Places` builds the restricted
  product; this record consumes it.
* `lift` is a chosen section of `pi`, not an existential. `T72` gives
  surjectivity and `D43` writes `Lift(tau)`; `tau_Addr` of `D46` is defined
  "for any `g in Lift(tau)`", and `T76a` is then the theorem that the choice
  did not matter. Making the choice data and proving independence is the only
  order in which `T76a` has content.
* `krep` is a chosen root representative of each class, which is what `D45`
  means by `Delta_K(k(x)) := [Delta(x)]`; `krep_act` is `D42`'s
  `pi(g)(k(x)) = k(g(x))` read on representatives, where the sign disjunction
  is `K = R/{+1,-1}` of `D12`. -/

/-- The data of sections 13 and 18 that section 18's functors are built from. -/
public structure LocData where
  /-- `O`: the rank of `V` in the `Sim` basis. `T65`'s `rank_Q(V) = O`. -/
  rank : Nat
  /-- `D33`: the places. -/
  Place : Type
  /-- `D33`: `Qv(v)`, with its `iota_v`. -/
  Qv : Place → QAlg
  /-- `D38`: the coefficient ring of the restricted product. -/
  Adr : QAlg
  /-- The place components of an address. -/
  proj : (v : Place) → RingHom Adr.Car (Qv v).Car
  /-- `D39`: the `v`-component of `Delta(x)` is `loc_v(x)`. -/
  proj_str : ∀ (v : Place) (q : Rat), (proj v).toFun (Adr.str.toFun q) = (Qv v).str.toFun q
  /-- `D41`: `WLin`. -/
  wlin : MatGroup rank
  /-- `D21`: `Aut`. -/
  aut : GrpData
  /-- `D42`: `pi : WLin -> Aut`. -/
  pi : wlin.El → aut.El
  pi_mul : ∀ g h : wlin.El, pi (wlin.grp.mul g h) = aut.mul (pi g) (pi h)
  /-- `T72`: `pi` is surjective, so `D43`'s `Lift(tau)` is nonempty; this is one
  choice from it. -/
  lift : aut.El → wlin.El
  pi_lift : ∀ t, pi (lift t) = t
  /-- `T73`: `ker(pi) <= {+I,-I}`, so a lift is unique up to one global sign. -/
  ker_pi : ∀ g : wlin.El, pi g = aut.one → g.val = Mat.id ∨ g.val = Mat.neg Mat.id
  /-- `D12`: the root classes `K`. -/
  KSet : Type
  /-- `D21`: the `Aut` action on `K`. -/
  kact : aut.El → KSet → KSet
  kact_one : ∀ κ, kact aut.one κ = κ
  kact_mul : ∀ (s t : aut.El) (κ : KSet), kact (aut.mul s t) κ = kact s (kact t κ)
  /-- `D45`: the representative root at which `Delta_K` is computed. -/
  krep : KSet → Vec rank Rat
  /-- `D42` on representatives, with `K = R/{+1,-1}`. -/
  krep_act : ∀ (g : wlin.El) (κ : KSet),
    krep (kact (pi g) κ) = Mat.apply g.val (krep κ)
      ∨ krep (kact (pi g) κ) = AddCommGroup.neg (Mat.apply g.val (krep κ))

namespace LocData

variable (L : LocData)

/-- `pi` carries the unit to the unit. Derived rather than assumed: a map that
preserves products carries the only idempotent of a group to the unit. -/
public theorem pi_one : L.pi L.wlin.grp.one = L.aut.one :=
  L.aut.eq_one_of_self_mul (by rw [← L.pi_mul, L.wlin.grp.one_mul])

end LocData

/-! ## Section-13 data defined here

`UorAtlas.Places` owns `D33`-`D51`. It was not importable when this module was
written, so the three constructions section 18 consumes are given here under
descriptive names -- deliberately **not** under the labels `D39`, `D44`, `D45`
or `D46`, because those labels belong to the module that states them. When
`UorAtlas.Places` lands, its versions replace these and the names below become
abbreviations of them.

`Addr(L)` itself is not reconstructed: it is `Vec L.rank L.Adr.Car`, the
restricted product in the coordinates of `V65c`'s basis. -/

/-- `D38`'s `Addr(L)`, in coordinates. -/
public abbrev Addr (L : LocData) : Type := Vec L.rank L.Adr.Car

/-- `D35`'s `loc_v : V -> V_v`, in coordinates: extension of scalars along
`iota_v`. -/
@[expose] public def locv (L : LocData) (v : L.Place) (x : Vec L.rank Rat) :
    Vec L.rank (L.Qv v).Car := Vec.map (L.Qv v).str x

/-- `D39`'s `Delta : V -> Addr(L)`, in coordinates. -/
@[expose] public def Delta (L : LocData) (x : Vec L.rank Rat) : Addr L := Vec.map L.Adr.str x

/-- `D44`'s `PAddr(L) := Addr(L)/{+1,-1}_diag`: the orbit set of the diagonal
sign action, which `RingLemmas.signAct` is. -/
public abbrev PAddr (L : LocData) : Type :=
  Quot (RingLemmas.OrbitRel (@RingLemmas.signAct (Addr L) _))

/-- The class of an address in `PAddr(L)`. -/
@[expose] public def paddrMk (L : LocData) (x : Addr L) : PAddr L :=
  Quot.mk (RingLemmas.OrbitRel (@RingLemmas.signAct (Addr L) _)) x

/-- An address and its negative have the same class: the single global sign of
`D44`. -/
public theorem paddrMk_neg (L : LocData) (x : Addr L) :
    paddrMk L (AddCommGroup.neg x) = paddrMk L x :=
  Quot.sound ⟨true, neg_neg x⟩

/-- The action of one element of `WLin` on `Addr(L)`: extension of scalars of
its matrix, then the matrix action. This is the `g_v` of `D43` assembled over
all places at once. -/
@[expose] public def addrAct (L : LocData) (g : L.wlin.El) (x : Addr L) : Addr L :=
  Mat.apply (Mat.map L.Adr.str g.val) x

/-- The action is equivariant for the diagonal sign, which is the hypothesis
`QL1` takes; the content is `M4`. -/
public theorem addrAct_neg (L : LocData) (g : L.wlin.El) (x : Addr L) :
    addrAct L g (AddCommGroup.neg x) = AddCommGroup.neg (addrAct L g x) :=
  apply_neg _ x

/-- `D46`'s `tau_Addr`, at the chosen lift. `T76a` below is that the choice did
not matter, and `F15a` that this is an action of `Aut`. -/
@[expose] public def tauAddr (L : LocData) (t : L.aut.El) : PAddr L → PAddr L :=
  RingLemmas.QL1.descend RingLemmas.signAct RingLemmas.signAct (addrAct L (L.lift t))
    (fun b x => by
      cases b with
      | true => exact addrAct_neg L (L.lift t) x
      | false => rfl)

public theorem tauAddr_mk (L : LocData) (t : L.aut.El) (x : Addr L) :
    tauAddr L t (paddrMk L x) = paddrMk L (addrAct L (L.lift t) x) := rfl

/-- `D45`'s `Delta_K : K -> PAddr(L)`, `Delta_K(k(x)) := [Delta(x)]`, computed
at the chosen representative root of the class. -/
@[expose] public def DeltaK (L : LocData) (κ : L.KSet) : PAddr L :=
  paddrMk L (Delta L (L.krep κ))

/-! ## The two target categories of `D64`'s table

`D64` writes `QMod` and `Set` and defines neither; they are the ambient
categories of `Q`-modules and of sets. `Cat.Ob` is a `Type`, so neither can be
taken whole -- the type of all `Q`-modules is not a `Type`. What section 18
needs, and all it needs, is that `R_Q`, `R_v` and `R_Addr` land in **one**
category and that `Kf` and `Pf` land in **one** category, because that is what
makes `F13`-`F15` type. So each is built as the full subcategory on exactly the
objects the section names, with genuine `Q`-linear maps and genuine functions
as morphisms.

Every object of `QMod` here is `Vec O A` for a `QAlg` `A`, with its `Q`-module
structure by restriction of scalars along `A`'s structure map. That is `D65`
read literally: `R_Q(*) = V`, `R_v(*) = Res_Q^{Qv(v)} V_v`, and
`R_Addr(*) = Addr(L)`, and the restriction of scalars is why `R_v` lands in
`QMod` at all. -/

/-- The objects of `QMod`: the three `Q`-modules of `D65`. -/
public inductive QIx (L : LocData) where
  /-- `V`, the rational carrier of `D34`. -/
  | rational : QIx L
  /-- `Res_Q^{Qv(v)} V_v`, the value of `R_v`. -/
  | localAt : L.Place → QIx L
  /-- `Addr(L)`, the value of `R_Addr`. -/
  | address : QIx L

/-- The coefficient algebra of each object. -/
@[expose] public def QIx.alg {L : LocData} : QIx L → QAlg
  | .rational => QAlg.rat
  | .localAt v => L.Qv v
  | .address => L.Adr

/-- The carrier of each object. -/
public abbrev QCar {L : LocData} (i : QIx L) : Type := Vec L.rank (QIx.alg i).Car

/-- The `Q`-action, by restriction of scalars along the structure map. -/
@[expose] public def qsmul {L : LocData} (i : QIx L) (q : Rat) (x : QCar i) : QCar i :=
  Vec.smul ((QIx.alg i).str.toFun q) x

/-- A morphism of `QMod`: a `Q`-linear map. -/
public structure QLin {L : LocData} (i j : QIx L) where
  /-- The underlying map. -/
  toFun : QCar i → QCar j
  map_add : ∀ x y, toFun (AddCommGroup.add x y)
    = AddCommGroup.add (toFun x) (toFun y)
  map_smul : ∀ (q : Rat) (x : QCar i), toFun (qsmul i q x) = qsmul j q (toFun x)

public theorem QLin.ext {L : LocData} {i j : QIx L} {f g : QLin i j}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  obtain ⟨a, _, _⟩ := f
  obtain ⟨b, _, _⟩ := g
  have hab : a = b := funext h
  subst hab
  rfl

@[expose] public def QLin.id {L : LocData} (i : QIx L) : QLin i i where
  toFun x := x
  map_add _ _ := rfl
  map_smul _ _ := rfl

@[expose] public def QLin.comp {L : LocData} {i j k : QIx L} (f : QLin j k) (g : QLin i j) :
    QLin i k where
  toFun x := f.toFun (g.toFun x)
  map_add x y := by rw [g.map_add, f.map_add]
  map_smul q x := by rw [g.map_smul, f.map_smul]

/-- `QMod` of `D64`'s table, on the objects section 18 names. -/
@[expose] public def QMod (L : LocData) : Cat where
  Ob := QIx L
  Hom := QLin
  idm i := QLin.id i
  comp f g := QLin.comp f g
  id_comp _ := QLin.ext fun _ => rfl
  comp_id _ := QLin.ext fun _ => rfl
  assoc _ _ _ := QLin.ext fun _ => rfl

/-- The objects of `Set`: the two sets section 18 names. -/
public inductive SIx (L : LocData) where
  /-- `K`, the value of `Kf`. -/
  | classes : SIx L
  /-- `PAddr(L)`, the value of `Pf`. -/
  | paddr : SIx L

@[expose] public def SCar {L : LocData} : SIx L → Type
  | .classes => L.KSet
  | .paddr => PAddr L

/-- `Set` of `D64`'s table, on the objects section 18 names. -/
@[expose] public def SetCat (L : LocData) : Cat where
  Ob := SIx L
  Hom X Y := SCar X → SCar Y
  idm _ := fun x => x
  comp f g := fun x => f (g x)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The morphism of `QMod` a ring homomorphism between coefficient algebras
induces, when it commutes with the two structure maps. `loc_v` and `Delta` are
its two instances. -/
@[expose] public def baseHom {L : LocData} (i j : QIx L)
    (φ : RingHom (QIx.alg i).Car (QIx.alg j).Car)
    (hc : ∀ q : Rat, φ.toFun ((QIx.alg i).str.toFun q) = (QIx.alg j).str.toFun q) :
    QLin i j where
  toFun := Vec.map φ
  map_add x y := funext fun k => φ.map_add (x k) (y k)
  map_smul q x := funext fun k => by
    show φ.toFun (CommRing.mul ((QIx.alg i).str.toFun q) (x k))
      = CommRing.mul ((QIx.alg j).str.toFun q) (φ.toFun (x k))
    rw [φ.map_mul, hc q]

/-- The morphism of `QMod` a square matrix over the coefficient algebra
induces. Every value of `R_Q`, `R_v` and `R_Addr` is one of these. -/
@[expose] public def matHom {L : LocData} (i : QIx L)
    (M : Mat L.rank L.rank (QIx.alg i).Car) : QLin i i where
  toFun := Mat.apply M
  map_add := apply_add M
  map_smul q x := apply_smul M ((QIx.alg i).str.toFun q) x

public theorem matHom_id {L : LocData} (i : QIx L) :
    matHom i Mat.id = QLin.id i := QLin.ext (fun x => apply_id x)

public theorem matHom_mul {L : LocData} (i : QIx L)
    (A B : Mat L.rank L.rank (QIx.alg i).Car) :
    matHom i (Mat.mul A B) = QLin.comp (matHom i A) (matHom i B) :=
  QLin.ext (fun x => apply_mul A B x)


/-! ## `D62`: the linear model, and what of it is formalised

Section 17 leaves section 18 four constructions. Three are pure linear algebra
over `Q` and are given here; the fourth, `component_dims`, is not, and the
reason is recorded in the module header: eigenvalue multiplicities are not
expressible over `Z` or `Q` without the spectral machinery of section 16, and
this library carries no real numbers. `D62` is therefore the record of the
three that are, with no field standing in for the one that is not. -/

/-- The three constructions of the linear model that section 18 consumes:
the chosen linear lift of an automorphism, the induced representation on
`Sym^2(V)`, and the commutant of `WLin` in `End_Q(V)`.

`Sym^2(V)` is carried by its Gram matrices, on which `g` acts as
`S |-> g S g^T`; that is the representation, in coordinates. The commutant is
a predicate rather than a subspace because every use of it below is membership.

`component_dims` is **absent**, not renamed: the eigenspace dimensions of a
generic commutant element need eigenvalue multiplicities, which section 16
supplies over `RR` and which neither `Z` nor `Q` expresses. -/
public structure LinModel (L : LocData) where
  /-- `lift_linear`: the matrix of the chosen lift of an automorphism. -/
  liftLinear : L.aut.El → Mat L.rank L.rank Rat
  /-- `sym2_rep`: the action of `WLin` on `Sym^2(V)` in Gram coordinates. -/
  sym2Rep : L.wlin.El → Mat L.rank L.rank Rat → Mat L.rank L.rank Rat
  /-- `commutant`: the matrices commuting with every element of `WLin`. -/
  commutant : Mat L.rank L.rank Rat → Prop

/-- `D62`. The linear model of section 17 at the data of section 18. -/
@[expose] public def D62 (L : LocData) : LinModel L where
  liftLinear t := (L.lift t).val
  sym2Rep g S := Mat.mul (Mat.mul g.val S) (Mat.transpose g.val)
  commutant M := ∀ g : L.wlin.El, Mat.mul M g.val = Mat.mul g.val M

/-- `sym2_rep` is a representation and not merely an assignment: it carries a
product of `WLin` to the composite. `M2` and `Mat.transpose_mul` are its whole
content. -/
public theorem sym2Rep_mul (L : LocData) (g h : L.wlin.El)
    (S : Mat L.rank L.rank Rat) :
    (D62 L).sym2Rep (L.wlin.grp.mul g h) S
      = (D62 L).sym2Rep g ((D62 L).sym2Rep h S) := by
  show Mat.mul (Mat.mul (Mat.mul g.val h.val) S) (Mat.transpose (Mat.mul g.val h.val))
    = Mat.mul (Mat.mul g.val (Mat.mul (Mat.mul h.val S) (Mat.transpose h.val)))
        (Mat.transpose g.val)
  rw [Mat.transpose_mul, ← M2 g.val (Mat.mul h.val S) (Mat.transpose h.val),
    ← M2 g.val h.val S,
    M2 (Mat.mul (Mat.mul g.val h.val) S) (Mat.transpose h.val) (Mat.transpose g.val)]

/-! ## `D63`: `AtlLin`, and `F1`

`D41` puts `WLin` inside `GL_Q(V)`; `D63` makes its elements the morphisms of a
category with one object. `D64`'s table writes that category as `B WLin`, so
the delooping is given for an arbitrary group and `D63` is its value at
`WLin`. -/

/-- `B G`: the one-object category on a group. -/
@[expose] public def deloop (G : GrpData) : Cat where
  Ob := Unit
  Hom _ _ := G.El
  idm _ := G.one
  comp f g := G.mul f g
  id_comp f := G.one_mul f
  comp_id f := G.mul_one f
  assoc h g f := G.mul_assoc h g f

/-- `D63`. `AtlLin := B WLin`: one object, and the elements of `WLin` as its
morphisms. -/
@[expose] public def D63 (L : LocData) : Cat := deloop L.wlin.grp

/-- `F1`. Composition in `AtlLin` is associative and unital **for every
morphism**, and every morphism is invertible: the five laws are `M2`, `M3` and
the two inverse equations of `D41`. -/
public theorem F1 (L : LocData) (a b c : L.wlin.El) :
    Mat.mul (Mat.mul a.val b.val) c.val = Mat.mul a.val (Mat.mul b.val c.val)
      ∧ Mat.mul (Mat.id : Mat L.rank L.rank Rat) a.val = a.val
      ∧ Mat.mul a.val (Mat.id : Mat L.rank L.rank Rat) = a.val
      ∧ Mat.mul (L.wlin.invOf a.val a.property) a.val = Mat.id
      ∧ Mat.mul a.val (L.wlin.invOf a.val a.property) = Mat.id :=
  ⟨M2 a.val b.val c.val, (M3 a.val).1, (M3 a.val).2,
    L.wlin.invOf_mul a.property, L.wlin.mul_invOf a.property⟩


/-! ## `F2`-`F7`: extension of scalars, before any of it is called a functor

`D43` writes `g_v` for the extension of scalars of a morphism, and `D35`,
`D39` write `loc_v` and `Delta`. The six statements here are about those maps
alone; nothing below `F7` mentions a category, which is the order section 18
insists on. -/

/-- `D43`'s `g_v`: the matrix of `g` after extension of scalars along
`iota_v`. -/
@[expose] public def locMat (L : LocData) (v : L.Place) (g : L.wlin.El) :
    Mat L.rank L.rank (L.Qv v).Car := Mat.map (L.Qv v).str g.val

/-- `F2`. The matrix of a morphism after extension of scalars is that morphism
entry by entry along `iota_v`, and the map it defines is `Qv(v)`-linear -- not
merely `Q`-linear, which is what makes the restriction of scalars in `D65`'s
second row a restriction of something. -/
public theorem F2 (L : LocData) (v : L.Place) (g : L.wlin.El) :
    (∀ i j, locMat L v g i j = (L.Qv v).str.toFun (g.val i j))
      ∧ (∀ x y : Vec L.rank (L.Qv v).Car,
          Mat.apply (locMat L v g) (AddCommGroup.add x y)
            = AddCommGroup.add (Mat.apply (locMat L v g) x) (Mat.apply (locMat L v g) y))
      ∧ (∀ (c : (L.Qv v).Car) (x : Vec L.rank (L.Qv v).Car),
          Mat.apply (locMat L v g) (Vec.smul c x)
            = Vec.smul c (Mat.apply (locMat L v g) x)) :=
  ⟨fun _ _ => rfl, apply_add _, apply_smul _⟩

/-- `F3`. Extension of scalars preserves composition. `M1` supplies the entry
identity and `M2` the associativity it is read against. -/
public theorem F3 (L : LocData) (v : L.Place) (g h : L.wlin.El) :
    locMat L v (L.wlin.grp.mul g h) = Mat.mul (locMat L v g) (locMat L v h) :=
  M1 (L.Qv v).str g.val h.val

/-- `F4`. Extension of scalars preserves the unit. -/
public theorem F4 (L : LocData) (v : L.Place) :
    locMat L v L.wlin.grp.one = (Mat.id : Mat L.rank L.rank (L.Qv v).Car) :=
  RingLemmas.map_id (L.Qv v).str

/-- `F5`. Every `g_v` is invertible, with `(g^{-1})_v` as its inverse: the
image of `WLin` lies in `GL_{Qv(v)}(V_v)`. This is where the chosen inverse of
`D41` is used as a matrix rather than as an existential. -/
public theorem F5 (L : LocData) (v : L.Place) (g : L.wlin.El) :
    Mat.mul (locMat L v g) (locMat L v (L.wlin.grp.inv g)) = Mat.id
      ∧ Mat.mul (locMat L v (L.wlin.grp.inv g)) (locMat L v g) = Mat.id := by
  refine ⟨?_, ?_⟩
  · rw [← F3, L.wlin.grp.mul_inv g, F4]
  · rw [← F3, L.wlin.grp.inv_mul g, F4]

/-- `F6p`. One coordinate of the naturality square: `iota_v` commutes with the
`i`-th entry of a matrix action, which is `RH1` at the polynomial `M1`
exhibits. -/
public theorem F6p (L : LocData) (v : L.Place) (g : L.wlin.El)
    (x : Vec L.rank Rat) (i : Fin L.rank) :
    (L.Qv v).str.toFun (Mat.apply g.val x i) = Mat.apply (locMat L v g) (locv L v x) i :=
  RingLemmas.RH1_apply (L.Qv v).str g.val x i

/-- `F6`. Localising after `g` is `g_v` after localising: the naturality square
of `loc_v`, before it is called one. Section 13 states the same equation as
`T79`. -/
public theorem F6 (L : LocData) (v : L.Place) (g : L.wlin.El) (x : Vec L.rank Rat) :
    locv L v (Mat.apply g.val x) = Mat.apply (locMat L v g) (locv L v x) :=
  funext (F6p L v g x)

/-- `F7`. The `v`-component of `Delta(x)` is `loc_v(x)`, at every place at once:
`D39`'s defining property of the diagonal, and the equation `F21`'s cone is
built on. -/
public theorem F7 (L : LocData) (v : L.Place) (x : Vec L.rank Rat) :
    Vec.map (L.proj v) (Delta L x) = locv L v x :=
  funext fun i => L.proj_str v (x i)


/-! ## `D64` and `D65`: the signature table, and the assignments it types

`D64` is the table. Its five fields are the five rows, and their **types** are
the signatures: two categories each, fixed before any assignment is written.
Inhabiting it is therefore the machine check section 20.1 asks for -- a row
whose source or target is wrong cannot be filled at all.

`D65` is the other half: the object and morphism assignments, as data with no
law attached. The functoriality theorems below are about these assignments, and
the `CatFunctor` records are bundled only after them. -/

/-- `D64`. The signature table of section 18: five rows, five field types.

* `RQ    : AtlLin -> QMod`, `R_Q(*) = V`;
* `Rv v  : AtlLin -> QMod`, `R_v(*) = Res_Q^{Qv(v)} V_v`, one row per place;
* `RAddr : AtlLin -> QMod`, `R_Addr(*) = Addr(L)`;
* `Kf    : B Aut -> Set`, `Kf(*) = K`;
* `Pf    : B Aut -> Set`, `Pf(*) = PAddr(L)`. -/
public structure D64 (L : LocData) where
  /-- Row 1: the rational representation. -/
  RQ : CatFunctor (D63 L) (QMod L)
  /-- Row 2: the local representation at each place. -/
  Rv : (v : L.Place) → CatFunctor (D63 L) (QMod L)
  /-- Row 3: the adelic representation. -/
  RAddr : CatFunctor (D63 L) (QMod L)
  /-- Row 4: the root classes as an `Aut`-set. -/
  Kf : CatFunctor (deloop L.aut) (SetCat L)
  /-- Row 5: `PAddr(L)` as an `Aut`-set. -/
  Pf : CatFunctor (deloop L.aut) (SetCat L)

/-- The object and morphism assignments of the five rows, without their laws.
`D65` is the one of these section 18 names. -/
public structure Assignments (L : LocData) where
  /-- `R_Q(*)`. -/
  qObj : QIx L
  /-- `R_Q(g)`. -/
  qMap : L.wlin.El → QLin qObj qObj
  /-- `R_v(*)`. -/
  vObj : L.Place → QIx L
  /-- `R_v(g) = g_v`. -/
  vMap : (v : L.Place) → L.wlin.El → QLin (vObj v) (vObj v)
  /-- `R_Addr(*)`. -/
  aObj : QIx L
  /-- `R_Addr(g)`. -/
  aMap : L.wlin.El → QLin aObj aObj
  /-- `Kf(*)`. -/
  kObj : SIx L
  /-- `Kf(tau)`, the action of `D21`. -/
  kMap : L.aut.El → SCar kObj → SCar kObj
  /-- `Pf(*)`. -/
  pObj : SIx L
  /-- `Pf(tau) = tau_Addr`, of `D46`. -/
  pMap : L.aut.El → SCar pObj → SCar pObj

/-- `D65`. The assignments: `V`, `V_v` by restriction of scalars, `Addr(L)`,
`K` and `PAddr(L)` on objects; the matrix action, its base changes, the `Aut`
action on classes and `tau_Addr` on morphisms. -/
@[expose] public def D65 (L : LocData) : Assignments L where
  qObj := QIx.rational
  qMap g := matHom QIx.rational g.val
  vObj v := QIx.localAt v
  vMap v g := matHom (QIx.localAt v) (locMat L v g)
  aObj := QIx.address
  aMap g := matHom QIx.address (Mat.map L.Adr.str g.val)
  kObj := SIx.classes
  kMap t κ := L.kact t κ
  pObj := SIx.paddr
  pMap t := tauAddr L t

/-- The morphism assignment of the third row is the action of `D43` assembled
over all places, which is how `F19` and `F21` reach `RP1`. -/
public theorem D65_aMap_apply (L : LocData) (g : L.wlin.El) (x : Addr L) :
    ((D65 L).aMap g).toFun x = addrAct L g x := rfl

/-! ## `F12`: why `F8`-`F11` were withdrawn

`F9` paired `Id : AtlLin -> AtlLin` with `Loc_v : AtlLin -> AtlLin_v`. A
component at `X` would be a morphism from `Id(X)` to `Loc_v(X)`, and those two
objects live in different categories, so there is no hom-set to draw it from;
`F10` and `F11` inherited the gap and `F8` was folded into `F17`.

`Across` is that demand written down: to give the components at all one must
first identify the two targets, and the identification is a field. `F12` reads
it back off. Section 20.1's fix -- "the signature table of `D65` makes this a
machine check rather than a reading" -- is then exactly that `NatTrans` takes
one pair of categories and `D64`'s rows fix which pair each row has. -/

/-- The pairing `F9` asserted: components for two functors out of `C` whose
targets need not agree. Writing one costs an identification of the targets,
which is the field `same`. -/
public structure Across {C D D' : Cat} (F : CatFunctor C D) (G : CatFunctor C D') where
  /-- The identification the components cannot be written without. -/
  same : D' = D
  /-- The components, in the single category the identification produces. -/
  app : (X : C.Ob) → D.Hom (F.obj X) (Eq.mp (congrArg Cat.Ob same) (G.obj X))

/-- `F12`. `F8`-`F11` are retracted, and this is the law that retracts them: a
family of components across two functors exists only when their targets are the
same category. `Id : AtlLin -> AtlLin` and `Loc_v : AtlLin -> AtlLin_v` have
different targets, so no such family can be written, and with the targets equal
the family is a `ComponentFamily` and `F13`-`F15` apply. -/
public theorem F12 {C D D' : Cat} {F : CatFunctor C D} {G : CatFunctor C D'}
    (η : Across F G) : D' = D := η.same

/-- The converse half of `F12`, and what makes it a criterion rather than a
bare projection: once the two targets **are** the same category, a component
family is an `Across` with nothing transported. So the identification is the
whole of the obstruction, and `D64` supplies it row by row. -/
@[expose] public def Across.ofFamily {C D : Cat} {F G : CatFunctor C D}
    (η : ComponentFamily F G) : Across F G where
  same := rfl
  app := η


/-! ## `T76a`: the lift may be chosen, and the choice does not matter

`D46` defines `tau_Addr` "for any `g in Lift(tau)`". `LocData.lift` makes one
choice; `T76a` is the theorem that any other choice induces the same map on
`PAddr(L)`, and it is what makes the definition a definition. `T73` bounds the
ambiguity by `{+I,-I}` and `D44` divides by exactly that, so the two cancel:
`M4` is the whole of the second case. -/

/-- In a group, a right inverse is the inverse. Used to get `pi` of an inverse
without assuming `pi` is a homomorphism on inverses. -/
public theorem GrpData.eq_inv_of_mul_eq_one (G : GrpData) {a b : G.El}
    (h : G.mul a b = G.one) : a = G.inv b := by
  have h1 : G.mul (G.mul a b) (G.inv b) = G.mul G.one (G.inv b) := by rw [h]
  rw [G.mul_assoc, G.mul_inv, G.mul_one, G.one_mul] at h1
  exact h1

/-- `pi` carries inverses to inverses: `D42` gives products, and a map of
groups preserving products preserves inverses. -/
public theorem pi_inv (L : LocData) (g : L.wlin.El) :
    L.pi (L.wlin.grp.inv g) = L.aut.inv (L.pi g) :=
  L.aut.eq_inv_of_mul_eq_one (by rw [← L.pi_mul, L.wlin.grp.inv_mul, L.pi_one])

/-- The action of `WLin` on `Addr(L)` is multiplicative: `M1` moves the product
through base change and `M2` splits the action. -/
public theorem addrAct_mul (L : LocData) (g h : L.wlin.El) (x : Addr L) :
    addrAct L (L.wlin.grp.mul g h) x = addrAct L g (addrAct L h x) := by
  show Mat.apply (Mat.map L.Adr.str (Mat.mul g.val h.val)) x
    = Mat.apply (Mat.map L.Adr.str g.val) (Mat.apply (Mat.map L.Adr.str h.val) x)
  rw [M1, apply_mul]

/-- The unit acts trivially. -/
public theorem addrAct_one (L : LocData) (x : Addr L) :
    addrAct L L.wlin.grp.one x = x := by
  show Mat.apply (Mat.map L.Adr.str (Mat.id : Mat L.rank L.rank Rat)) x = x
  rw [RingLemmas.map_id]
  exact apply_id x

/-- `T76a`. Two lifts of the same automorphism induce the same map on
`PAddr(L)`. By `T73` they differ by a global sign, and `D44` is the quotient by
exactly that sign. -/
public theorem T76a (L : LocData) (g h : L.wlin.El) (hgh : L.pi g = L.pi h) (x : Addr L) :
    paddrMk L (addrAct L g x) = paddrMk L (addrAct L h x) := by
  have hk : L.pi (L.wlin.grp.mul g (L.wlin.grp.inv h)) = L.aut.one := by
    rw [L.pi_mul, pi_inv, hgh]
    exact L.aut.mul_inv _
  have hkh0 : L.wlin.grp.mul (L.wlin.grp.mul g (L.wlin.grp.inv h)) h = g := by
    rw [L.wlin.grp.mul_assoc, L.wlin.grp.inv_mul, L.wlin.grp.mul_one]
  have hkh : Mat.mul (L.wlin.grp.mul g (L.wlin.grp.inv h)).val h.val = g.val :=
    congrArg Subtype.val hkh0
  refine Or.elim (L.ker_pi _ hk) (fun hone => ?_) (fun hneg => ?_)
  · have hg : g.val = h.val := by
      rw [← hkh, hone]
      exact (M3 h.val).1
    show paddrMk L (Mat.apply (Mat.map L.Adr.str g.val) x)
      = paddrMk L (Mat.apply (Mat.map L.Adr.str h.val) x)
    rw [hg]
  · have hg : g.val = Mat.mul (Mat.neg Mat.id) h.val := by rw [← hkh, hneg]
    show paddrMk L (Mat.apply (Mat.map L.Adr.str g.val) x)
      = paddrMk L (Mat.apply (Mat.map L.Adr.str h.val) x)
    rw [hg, M1, map_neg_mat, RingLemmas.map_id, apply_mul, M4, apply_id]
    exact paddrMk_neg L _

/-! ## `F22`, `F17`, `F19a`, `F15a`, `F15p`: the assignments are functorial

Construction precedes typing. Each theorem here says of one row of `D65` that
it carries the unit to the identity and a product to the composite; nothing is
bundled into a `CatFunctor` until all five are proved. `F15p` is stated with
them rather than after `F15`, because `F15`'s type does not exist until `Kf`
is a functor. -/

/-- `F22`. `R_Q` is a functor: `M3` gives the unit and `M2` the composite. -/
public theorem F22 (L : LocData) :
    (D65 L).qMap L.wlin.grp.one = QLin.id ((D65 L).qObj)
      ∧ ∀ g h : L.wlin.El, (D65 L).qMap (L.wlin.grp.mul g h)
          = QLin.comp ((D65 L).qMap g) ((D65 L).qMap h) := by
  refine ⟨?_, fun g h => ?_⟩
  · show matHom QIx.rational (Mat.id : Mat L.rank L.rank Rat) = QLin.id _
    exact matHom_id _
  · show matHom QIx.rational (Mat.mul g.val h.val) = _
    exact matHom_mul _ _ _

/-- `F17`. `R_v` is a functor, at every place: `F4` gives the unit and `F3` the
composite, so this is `M1`-`M3` through base change. `F8` was folded into this
statement (section 20.1). -/
public theorem F17 (L : LocData) (v : L.Place) :
    (D65 L).vMap v L.wlin.grp.one = QLin.id ((D65 L).vObj v)
      ∧ ∀ g h : L.wlin.El, (D65 L).vMap v (L.wlin.grp.mul g h)
          = QLin.comp ((D65 L).vMap v g) ((D65 L).vMap v h) := by
  refine ⟨?_, fun g h => ?_⟩
  · show matHom (QIx.localAt v) (locMat L v L.wlin.grp.one) = QLin.id _
    rw [F4]
    exact matHom_id _
  · show matHom (QIx.localAt v) (locMat L v (L.wlin.grp.mul g h)) = _
    rw [F3]
    exact matHom_mul _ _ _

/-- `F19a`. `R_Addr` is a functor. The same argument as `F17` at the coefficient
ring of the restricted product, which is the only structure `RP1` leaves this
proof. -/
public theorem F19a (L : LocData) :
    (D65 L).aMap L.wlin.grp.one = QLin.id ((D65 L).aObj)
      ∧ ∀ g h : L.wlin.El, (D65 L).aMap (L.wlin.grp.mul g h)
          = QLin.comp ((D65 L).aMap g) ((D65 L).aMap h) := by
  refine ⟨?_, fun g h => ?_⟩
  · show matHom QIx.address (Mat.map L.Adr.str (Mat.id : Mat L.rank L.rank Rat)) = QLin.id _
    rw [RingLemmas.map_id]
    exact matHom_id _
  · show matHom QIx.address (Mat.map L.Adr.str (Mat.mul g.val h.val)) = _
    rw [M1]
    exact matHom_mul _ _ _

/-- `F15a`. `Pf` is a functor: `tau_Addr` is an action of `Aut` on `PAddr(L)`.
Both halves are `T76a`, because `lift(1)` and `lift(st)` are lifts of the same
automorphisms as `1` and `lift(s) lift(t)` but need not be those elements. -/
public theorem F15a (L : LocData) :
    (∀ κ : SCar ((D65 L).pObj), (D65 L).pMap L.aut.one κ = κ)
      ∧ ∀ (s t : L.aut.El) (κ : SCar ((D65 L).pObj)),
          (D65 L).pMap (L.aut.mul s t) κ = (D65 L).pMap s ((D65 L).pMap t κ) := by
  refine ⟨?_, ?_⟩
  · show ∀ κ : PAddr L, tauAddr L L.aut.one κ = κ
    refine Quot.ind (fun x => ?_)
    show paddrMk L (addrAct L (L.lift L.aut.one) x) = paddrMk L x
    rw [T76a L (L.lift L.aut.one) L.wlin.grp.one (by rw [L.pi_lift, L.pi_one]), addrAct_one]
  · intro s t
    show ∀ κ : PAddr L, tauAddr L (L.aut.mul s t) κ = tauAddr L s (tauAddr L t κ)
    refine Quot.ind (fun x => ?_)
    show paddrMk L (addrAct L (L.lift (L.aut.mul s t)) x)
      = paddrMk L (addrAct L (L.lift s) (addrAct L (L.lift t) x))
    rw [← addrAct_mul,
      T76a L (L.lift (L.aut.mul s t)) (L.wlin.grp.mul (L.lift s) (L.lift t))
        (by rw [L.pi_lift, L.pi_mul, L.pi_lift, L.pi_lift])]

/-- `F15p`. `Kf` is a functor: `D21`'s action of `Aut` on the root classes is an
action. This is the preparation `F15` needs -- without it `Kf` is not an object
of the source of a natural transformation and `F15` has no type. -/
public theorem F15p (L : LocData) :
    (∀ κ : SCar ((D65 L).kObj), (D65 L).kMap L.aut.one κ = κ)
      ∧ ∀ (s t : L.aut.El) (κ : SCar ((D65 L).kObj)),
          (D65 L).kMap (L.aut.mul s t) κ = (D65 L).kMap s ((D65 L).kMap t κ) :=
  ⟨L.kact_one, L.kact_mul⟩


/-! ## The five rows, bundled, and the table inhabited

Only now, with `F22`, `F17`, `F19a`, `F15a` and `F15p` proved, are the
`CatFunctor` records built: each takes its two laws from the theorem about the
matching row of `D65`, and none of them re-proves anything. Inhabiting `D64` is
then the machine check -- a row whose source or target were wrong could not be
filled. -/

/-- Row 1 of `D64`: `R_Q`. -/
@[expose] public def RQ (L : LocData) : CatFunctor (D63 L) (QMod L) where
  obj _ := (D65 L).qObj
  map g := (D65 L).qMap g
  map_id _ := (F22 L).1
  map_comp f g := (F22 L).2 f g

/-- Row 2 of `D64`: `R_v`, at one place. -/
@[expose] public def Rv (L : LocData) (v : L.Place) : CatFunctor (D63 L) (QMod L) where
  obj _ := (D65 L).vObj v
  map g := (D65 L).vMap v g
  map_id _ := (F17 L v).1
  map_comp f g := (F17 L v).2 f g

/-- Row 3 of `D64`: `R_Addr`. -/
@[expose] public def RAddr (L : LocData) : CatFunctor (D63 L) (QMod L) where
  obj _ := (D65 L).aObj
  map g := (D65 L).aMap g
  map_id _ := (F19a L).1
  map_comp f g := (F19a L).2 f g

/-- Row 4 of `D64`: `Kf`. -/
@[expose] public def Kf (L : LocData) : CatFunctor (deloop L.aut) (SetCat L) where
  obj _ := (D65 L).kObj
  map t := (D65 L).kMap t
  map_id _ := funext (F15p L).1
  map_comp f g := funext ((F15p L).2 f g)

/-- Row 5 of `D64`: `Pf`. -/
@[expose] public def Pf (L : LocData) : CatFunctor (deloop L.aut) (SetCat L) where
  obj _ := (D65 L).pObj
  map t := (D65 L).pMap t
  map_id _ := funext (F15a L).1
  map_comp f g := funext ((F15a L).2 f g)

/-- The table of `D64`, inhabited. Every row's signature is checked here, which
is what section 20.1 asks for in place of the withdrawn prose. -/
@[expose] public def signatureTable (L : LocData) : D64 L where
  RQ := RQ L
  Rv := Rv L
  RAddr := RAddr L
  Kf := Kf L
  Pf := Pf L

/-! ## `F13`-`F15`: the three transformations are well typed

These three are typing facts and nothing else, and the module is built so that
the type checker certifies them: `ComponentFamily F G` mentions **one** source
category and **one** target category, so writing `loc_v` at the type
`ComponentFamily R_Q R_v` at all forces `R_Q` and `R_v` to agree in both. Lean
accepting the three declarations below **is** the proof; there is no separate
obligation, which is exactly what `F12` says the fix must look like.

The squares that make them natural transformations are `F16`, `F19` and `F20`,
and each is bundled into a `NatTrans` beside its square. -/

/-- `loc_v` as a morphism of `QMod`: extension of scalars along `iota_v`, which
is `Q`-linear because `iota_v` is a `Q`-algebra map. -/
@[expose] public def locHom (L : LocData) (v : L.Place) :
    QLin (QIx.rational : QIx L) (QIx.localAt v) :=
  baseHom QIx.rational (QIx.localAt v) (L.Qv v).str (fun _ => rfl)

/-- `Delta` as a morphism of `QMod`. -/
@[expose] public def deltaHom (L : LocData) :
    QLin (QIx.rational : QIx L) QIx.address :=
  baseHom QIx.rational QIx.address L.Adr.str (fun _ => rfl)

/-- The `v`-th place projection as a morphism of `QMod`; `D39`'s compatibility
is what makes it `Q`-linear. -/
@[expose] public def projHom (L : LocData) (v : L.Place) :
    QLin (QIx.address : QIx L) (QIx.localAt v) :=
  baseHom QIx.address (QIx.localAt v) (L.proj v) (L.proj_str v)

/-- `F13`. `loc_v : R_Q => R_v` is well typed. Both functors go from `AtlLin`
to `QMod`, so the component family can be written; that Lean checks this
declaration is the whole of the claim. -/
@[expose] public def F13 (L : LocData) (v : L.Place) :
    ComponentFamily (RQ L) (Rv L v) := fun _ => locHom L v

/-- `F14`. `Delta : R_Q => R_Addr` is well typed. -/
@[expose] public def F14 (L : LocData) : ComponentFamily (RQ L) (RAddr L) :=
  fun _ => deltaHom L

/-- `F15`. `Delta_K : Kf => Pf` is well typed. Both go from `B Aut` to `Set`,
which is `F15p` and `F15a`; without those two this declaration has no type. -/
@[expose] public def F15 (L : LocData) : ComponentFamily (Kf L) (Pf L) :=
  fun _ => DeltaK L

/-- `F16`. The naturality square of `loc_v`: localising after `g` is `g_v`
after localising. `F6` is the same equation on vectors; section 13 states it as
`T79`. -/
public theorem F16 (L : LocData) (v : L.Place) (g : L.wlin.El) :
    (QMod L).comp (F13 L v ()) ((RQ L).map g)
      = (QMod L).comp ((Rv L v).map g) (F13 L v ()) :=
  QLin.ext (fun x => F6 L v g x)

/-- `loc_v` as a natural transformation `R_Q => R_v`, its components `F13` and
its square `F16`. -/
@[expose] public def locNat (L : LocData) (v : L.Place) : NatTrans (RQ L) (Rv L v) where
  app := F13 L v
  naturality f := F16 L v f


/-! ## `D66`, `D67`: the local family and the cone over it

`D66` names the family of local representations as a map of the places into the
functor category `[B WLin, QMod]`, which is what makes "one representation per
place" a diagram rather than a list. `D67` is the cone shape over that diagram:
an apex, a leg to each place, and the diagonal from `R_Q`. `F21` is then the
one equation a cone has to satisfy, and `F7` is its whole content. -/

/-- `D66`. `LocalRep`: the local representation at each place, as an object of
`[B WLin, QMod]`. -/
@[expose] public def D66 (L : LocData) : L.Place → (funCat (D63 L) (QMod L)).Ob :=
  fun v => Rv L v

/-- `F18`. The place projection is natural: projecting after `g` acts on
`Addr(L)` is `g_v` after projecting. `RH1` at the matrix action again, now
along `Addr(L) -> Qv(v)`, and `D39`'s compatibility identifies the two base
changes. -/
public theorem F18 (L : LocData) (v : L.Place) (g : L.wlin.El) :
    (QMod L).comp (projHom L v) ((RAddr L).map (X := ()) (Y := ()) g)
      = (QMod L).comp ((Rv L v).map (X := ()) (Y := ()) g) (projHom L v) := by
  have hmat : Mat.map (L.proj v) (Mat.map L.Adr.str g.val) = locMat L v g :=
    funext fun i => funext fun j => L.proj_str v (g.val i j)
  refine QLin.ext (fun x => ?_)
  show Vec.map (L.proj v) (Mat.apply (Mat.map L.Adr.str g.val) x)
    = Mat.apply (locMat L v g) (Vec.map (L.proj v) x)
  rw [map_apply, hmat]

/-- The place projection as a natural transformation `R_Addr => R_v`. -/
@[expose] public def projNat (L : LocData) (v : L.Place) : NatTrans (RAddr L) (Rv L v) where
  app _ := projHom L v
  naturality f := F18 L v f

/-- `F19`. The naturality square of `Delta`: the diagonal commutes with the
action of `WLin`, which is `RH1` at the coefficient ring of the restricted
product. -/
public theorem F19 (L : LocData) (g : L.wlin.El) :
    (QMod L).comp (F14 L ()) ((RQ L).map g)
      = (QMod L).comp ((RAddr L).map g) (F14 L ()) :=
  QLin.ext (fun x => map_apply L.Adr.str g.val x)

/-- `Delta` as a natural transformation `R_Q => R_Addr`, its components `F14`
and its square `F19`. -/
@[expose] public def deltaNat (L : LocData) : NatTrans (RQ L) (RAddr L) where
  app := F14 L
  naturality f := F19 L f

/-- `D67`. A cone over `LocalRep` with a diagonal from `R_Q`: the shape
`Addr(L)` sits in. The commuting condition is `F21`, stated of the cone this
module exhibits rather than assumed of every cone. -/
public structure D67 (L : LocData) where
  /-- The apex. -/
  apex : CatFunctor (D63 L) (QMod L)
  /-- The leg at each place. -/
  leg : (v : L.Place) → NatTrans apex (D66 L v)
  /-- The diagonal into the apex. -/
  diag : NatTrans (RQ L) apex

/-- The cone `D38` and `D39` build: `R_Addr` with the place projections as legs
and `Delta` as diagonal. -/
@[expose] public def adelicCone (L : LocData) : D67 L where
  apex := RAddr L
  leg v := projNat L v
  diag := deltaNat L

/-- `F20`. The naturality square of `Delta_K`: `Delta_K(tau . k) =
tau_Addr(tau)(Delta_K(k))`. `D42` moves the representative root by a lift of
`tau` up to sign, `M4` carries that sign through the action, and `D44` divides
by it. Section 13 states this equation as `T80`. -/
public theorem F20 (L : LocData) (t : L.aut.El) :
    (SetCat L).comp (F15 L ()) ((Kf L).map t)
      = (SetCat L).comp ((Pf L).map t) (F15 L ()) := by
  refine funext (fun κ => ?_)
  have hk := L.krep_act (L.lift t) κ
  rw [L.pi_lift] at hk
  show paddrMk L (Delta L (L.krep (L.kact t κ)))
    = paddrMk L (addrAct L (L.lift t) (Delta L (L.krep κ)))
  refine Or.elim hk (fun h1 => ?_) (fun h1 => ?_)
  · rw [h1]
    show paddrMk L (Vec.map L.Adr.str (Mat.apply (L.lift t).val (L.krep κ)))
      = paddrMk L (Mat.apply (Mat.map L.Adr.str (L.lift t).val)
          (Vec.map L.Adr.str (L.krep κ)))
    rw [map_apply]
  · rw [h1]
    show paddrMk L (Vec.map L.Adr.str (AddCommGroup.neg (Mat.apply (L.lift t).val (L.krep κ))))
      = paddrMk L (Mat.apply (Mat.map L.Adr.str (L.lift t).val)
          (Vec.map L.Adr.str (L.krep κ)))
    rw [map_neg_vec, map_apply, paddrMk_neg]

/-- `Delta_K` as a natural transformation `Kf => Pf`, its components `F15` and
its square `F20`. -/
@[expose] public def deltaKNat (L : LocData) : NatTrans (Kf L) (Pf L) where
  app := F15 L
  naturality f := F20 L f

/-- `F21`. The cone commutes: at every place, the leg after the diagonal is
`loc_v`. This is `F7` -- `D39`'s "the `v`-component of `Delta(x)` is
`loc_v(x)`" -- read as an equation of natural transformations, which is the
form in which it says that `Addr(L)` localises compatibly at every place at
once. -/
public theorem F21 (L : LocData) (v : L.Place) :
    NatTrans.vcomp ((adelicCone L).leg v) (adelicCone L).diag = locNat L v :=
  NatTrans.ext (fun _ => QLin.ext (fun x => F7 L v x))

end UorAtlas.Functor
