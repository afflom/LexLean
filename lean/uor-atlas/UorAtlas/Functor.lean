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

end UorAtlas.Functor
