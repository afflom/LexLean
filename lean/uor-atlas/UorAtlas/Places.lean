module
public import Init
public import UorAtlas.Prelude.Algebra
public import UorAtlas.Prelude.Linear
public import UorAtlas.Prelude.NumInstances
public import UorAtlas.Prelude.RingLemmas
public import UorAtlas.Roots

/-!
Section 13 of `UOR-ATLAS-FORMAL-001`: places, localization, and the diagonal
coupling.

## The ring is a parameter, not a construction

Section 4.4 of the release plan fixes the route: "`BC1` through the
ring-parameterized section 13 rather than a constructed `Z_p`". So no
completion is built here. A `Place` is a *record of rings* -- local integers
`Z_v` inside an ambient `Q_v`, both receiving the section-0 structure maps
`Z -> Z_v` and `iota_v : Q -> Q_v` -- and every statement about `L_v`, `V_v`,
the local dual and the local action becomes a statement about base change along
those maps. `BC1` and `SD1` of `UorAtlas.Prelude.RingLemmas` are already stated
in exactly that generality, so `V69` and `V72` are their instances rather than
new arguments.

The parameterization would be worthless if nothing satisfied it, so the places
are also *exhibited*: `placeAt` is the localization `Z_(p) = { q : Q : p does
not divide den(q) } ⊂ Q` at every prime, built here as a genuine subring, and
`locSystem` assembles those into a system of places indexed by the primes.
`Z_(p)` is the localization and not the completion, which is the point --- the
document's `Z_p` receives it, and every statement below is preserved under that
further map because every statement below is about an arbitrary ring receiving
`Z`.

## The coordinates everything is written in

`V65c` says `Sim` is a `Z`-basis of `L`, and it is proved here rather than
assumed, because it is what licenses writing `L_v` as "coordinate vectors with
entries in `Z_v`" and the form as its Gram matrix. The proof is the document's
own: `T58x` gives `det Gram(Sim) = 1`, `T57b` at `n = 8` gives that the form is
integral on `L`, and those two turn the pairings `<y, a_j>` into integer
coordinates. The two integer matrices this needs -- the inverse of `Gram(Sim)`
and the table `dualBasis` that inverts `Sim` itself up to the scaling factor
`4` -- are computed outside and *checked* inside by `decide +kernel`; nothing
is searched for in the kernel.

Because `Gram(Sim)` is unimodular (`T58x`), its base change to any `Z_v` is
invertible (`BC1`), and `SD1` then gives `V69`: `L_v` is its own dual, at every
place at once.

## `Addr(L)` and `RP1`

`D38` is the restricted product: a family of local vectors, integral at all but
finitely many places. Finiteness is containment in a list, the only notion
available without `Finset`, and it is the notion the document's own
"bad-denominator set" argument produces. `RP1` is then the `Q`-module structure
on that product, and its whole content is that scaling by a rational preserves
the almost-everywhere condition: a rational has finitely many denominator
primes, which is `DV1`. `V70` is the same finiteness for a whole rational
vector and is exactly what makes the diagonal embedding `V -> Addr(L)` land in
the restricted product at all.

## What is not here, and why

`T65` to `T83` -- including `T76a`, `T77a`, `T80p` and `T80a` -- together with
`V71`, `V73`, `V75` and the definitions `D33`, `D36`, `D39` to `D43`, and `D45`
to `D51a` apart from `D46a`, which `UorAtlas.Blocks` carries, are absent.

The text of section 13 was not available to this pass. A label is a claim about
the *document* and not merely about the mathematics, so a declaration named
`T71` that states something the document does not state is worse than no
declaration at all: a reader who greps for the label finds an answer, and the
answer is unverifiable against the source. The same reasoning is recorded in
`UorAtlas.Category` for `T47` and `T61` to `T64`.

Every label named below is instead one whose statement is fixed by text this
repository already carries: `UorAtlas.Prelude.RingLemmas` quotes `D34`, `D37`,
`D44`, `V65c`, `V69`, `V70`, `V72` and `V74`, and `UorAtlas.Prelude.Linear`
quotes `D35` and `D35a`; `RP1` is fixed by the ambient-lemma register of
section 19.6, which this repository reproduces in
`language/uor/atlas-registers.toml`.

The machinery the absent labels would be stated against is built here
regardless -- the places, the local lattice and its dual, the restricted
product, the `Q`-module structure and the diagonal descent -- so supplying them
is a matter of reading section 13, not of further construction.
-/

set_option autoImplicit false

namespace UorAtlas.Places

open UorAtlas.Prelude
open UorAtlas.Prelude.Linear
open UorAtlas.Prelude.RingLemmas

universe u v w

/-! ## Integer double sums

`V65c` is a coordinate computation, so it needs Fubini and the two distributive
laws on `Vec.sumInt`. `Vec.sum` has them over any `AddCommGroup`; these are the
same facts on the concrete integer sum, bridged once through `sumInt_eq_sum`
rather than at every step. -/

public theorem sumInt_exchange {m n : Nat} (f : Fin m → Fin n → Int) :
    Vec.sumInt (fun i => Vec.sumInt (fun j => f i j))
      = Vec.sumInt (fun j => Vec.sumInt (fun i => f i j)) := by
  have h1 : Vec.sumInt (fun i => Vec.sumInt (fun j => f i j))
      = Vec.sum (fun i => Vec.sum (fun j => f i j)) := by
    rw [Vec.sumInt_eq_sum]; exact Vec.sum_congr (fun i => Vec.sumInt_eq_sum _)
  have h2 : Vec.sumInt (fun j => Vec.sumInt (fun i => f i j))
      = Vec.sum (fun j => Vec.sum (fun i => f i j)) := by
    rw [Vec.sumInt_eq_sum]; exact Vec.sum_congr (fun j => Vec.sumInt_eq_sum _)
  rw [h1, h2, Vec.sum_exchange]

public theorem sumInt_mul_right {n : Nat} (x : Vec n Int) (c : Int) :
    Vec.sumInt (fun i => x i * c) = Vec.sumInt x * c := by
  rw [Int.mul_comm, ← Glue.sumInt_mul_left]
  exact Glue.sumInt_congr (fun i => Int.mul_comm (x i) c)

public theorem sumInt_ite_eq {n : Nat} (i : Fin n) (x : Vec n Int) :
    Vec.sumInt (fun k => if i = k then x k else 0) = x i := by
  rw [Vec.sumInt_eq_sum]
  exact Vec.sum_ite_eq i x

/-! ## The two checked tables

Both matrices below are computed outside the kernel and checked inside it. The
check is a `Mat.mul` identity at size `8`, which `decide +kernel` settles
directly; nothing here searches. -/

/-- The inverse of `Gram(Sim)`. It is an integer matrix because `T58x` says the
determinant is `1`. -/
@[expose] public def gramInvRows : List (List Int) :=
  [[ 4,  5,  7, 10,  8,  6,  4,  2], [ 5,  8, 10, 15, 12,  9,  6,  3],
   [ 7, 10, 14, 20, 16, 12,  8,  4], [10, 15, 20, 30, 24, 18, 12,  6],
   [ 8, 12, 16, 24, 20, 15, 10,  5], [ 6,  9, 12, 18, 15, 12,  8,  4],
   [ 4,  6,  8, 12, 10,  8,  6,  3], [ 2,  3,  4,  6,  5,  4,  3,  2]]

@[expose] public def gramInv : Mat 8 8 Int :=
  fun i j => ((gramInvRows.getD i.val []).getD j.val 0)

/-- `Gram(Sim)^{-1} Sim`, the dual family of `Sim` scaled by `4`. The scaling
is the same doubling `UorAtlas.Glue` fixes: an unscaled value `v` appears as the
integer `4v`, so the dual basis of an integral basis is integral after
multiplication by `4` and not before. -/
@[expose] public def dualRows : List (List Int) :=
  [[0, 1, -1, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0, 0],
   [0, 1,  1, 2, 0, 0, 0, 0], [0, 1, 1, 2, 2, 0, 0, 0],
   [0, 1,  1, 2, 2, 2, 0, 0], [0, 1, 1, 2, 2, 2, 2, 0],
   [0, 1,  1, 2, 2, 2, 2, 2], [4, 5, 7, 10, 8, 6, 4, 2]]

@[expose] public def dualBasis : Mat 8 8 Int :=
  fun i j => ((dualRows.getD i.val []).getD j.val 0)

public theorem gramInv_right (i j : Fin 8) :
    Mat.mul Roots.gram gramInv i j = (Mat.id : Mat 8 8 Int) i j := by
  revert i j; decide +kernel

public theorem gramInv_left (i j : Fin 8) :
    Mat.mul gramInv Roots.gram i j = (Mat.id : Mat 8 8 Int) i j := by
  revert i j; decide +kernel

/-- `Gram(Sim) in GL_8(Z)`. This is `T58x` in the form `SD1` consumes: `SD1`
asks for a two-sided inverse rather than for a unit determinant, because over a
general ring the passage between the two is the adjugate and every consumer
wants the inverse matrix itself. -/
public theorem gram_InGL : InGL Roots.gram :=
  ⟨gramInv, funext fun i => funext fun j => gramInv_right i j,
    funext fun i => funext fun j => gramInv_left i j⟩

public theorem gramInv_sim (k m : Fin 8) :
    Vec.sumInt (fun i => gramInv k i * Roots.D19a i m) = dualBasis m k := by
  revert k m; decide +kernel

public theorem dual_sim (m l : Fin 8) :
    Vec.sumInt (fun k => dualBasis m k * Roots.D19a k l) = if m = l then (4 : Int) else 0 := by
  revert m l; decide +kernel

public theorem sim_dual (i j : Fin 8) :
    Vec.sumInt (fun m => Roots.D19a i m * dualBasis m j) = if j = i then (4 : Int) else 0 := by
  revert i j; decide +kernel

/-! ## `V65c`: `Sim` is a `Z`-basis of `L`

The coordinates of `y` are read off its pairings against the simple roots. Two
document facts make them integers: the form is integral on `L` (`T57b` at
`n = 8`, so `4 | <y, a_j>` in the doubled scaling), and `Gram(Sim)` is
unimodular (`T58x`). Nondegeneracy -- that the reconstruction really returns
`y` -- is the `dualBasis` identity, which is the same unimodularity read on
`Sim` instead of on its Gram matrix. -/

public theorem simMemL (j : Fin 8) : Glue.MemL 8 (Roots.D19a j) :=
  ((Roots.D11_iff _).mp (Roots.V65a.1 j)).1

/-- `L_8` is an integral lattice: `T57b` at the one dimension the Atlas uses. -/
public theorem integral8 : Glue.Integral 8 := (Glue.T57b 8).mpr (by decide)

public theorem pair_dvd {y : Vec 8 Int} (hy : Glue.MemL 8 y) (j : Fin 8) :
    (4 : Int) ∣ dot y (Roots.D19a j) := integral8 y _ hy (simMemL j)

/-- `<y, a_j>` in the document's normalisation: the doubled form divided by the
`4` that `pair_dvd` certifies exact. -/
@[expose] public def pairing (y : Vec 8 Int) (j : Fin 8) : Int := dot y (Roots.D19a j) / 4

public theorem pairing_spec {y : Vec 8 Int} (hy : Glue.MemL 8 y) (j : Fin 8) :
    4 * pairing y j = dot y (Roots.D19a j) :=
  Int.mul_ediv_cancel' (pair_dvd hy j)

/-- The `Sim`-coordinates of a lattice vector. -/
@[expose] public def simCoord (y : Vec 8 Int) (i : Fin 8) : Int :=
  Vec.sumInt (fun k => pairing y k * gramInv k i)

public theorem simCoord_comb (y : Vec 8 Int) (m : Fin 8) :
    Vec.sumInt (fun i => simCoord y i * Roots.D19a i m)
      = Vec.sumInt (fun k => pairing y k * dualBasis m k) := by
  have step : Vec.sumInt (fun i => simCoord y i * Roots.D19a i m)
      = Vec.sumInt (fun i => Vec.sumInt (fun k => pairing y k * gramInv k i * Roots.D19a i m)) :=
    Glue.sumInt_congr (fun i => (sumInt_mul_right _ _).symm)
  rw [step, sumInt_exchange (fun i k => pairing y k * gramInv k i * Roots.D19a i m)]
  refine Glue.sumInt_congr (fun k => ?_)
  rw [Glue.sumInt_congr
      (fun i => Int.mul_assoc (pairing y k) (gramInv k i) (Roots.D19a i m)),
    Glue.sumInt_mul_left, gramInv_sim k m]

public theorem recon {y : Vec 8 Int} (hy : Glue.MemL 8 y) (m : Fin 8) :
    y m = Vec.sumInt (fun i => simCoord y i * Roots.D19a i m) := by
  rw [simCoord_comb y m]
  refine (Int.eq_of_mul_eq_mul_left (a := 4) (by decide) ?_).symm
  have h1 : (4 : Int) * Vec.sumInt (fun k => pairing y k * dualBasis m k)
      = Vec.sumInt (fun k => dot y (Roots.D19a k) * dualBasis m k) := by
    rw [← Glue.sumInt_mul_left]
    refine Glue.sumInt_congr (fun k => ?_)
    rw [← Int.mul_assoc, pairing_spec hy k]
  have h2 : ∀ k : Fin 8, dot y (Roots.D19a k) * dualBasis m k
      = Vec.sumInt (fun l => y l * (Roots.D19a k l * dualBasis m k)) := by
    intro k
    rw [Glue.dot_def, ← sumInt_mul_right]
    exact Glue.sumInt_congr (fun l => Int.mul_assoc _ _ _)
  rw [h1, Glue.sumInt_congr h2,
    sumInt_exchange (fun k l => y l * (Roots.D19a k l * dualBasis m k))]
  have h3 : ∀ l : Fin 8, Vec.sumInt (fun k => y l * (Roots.D19a k l * dualBasis m k))
      = y l * (if m = l then (4 : Int) else 0) := by
    intro l
    rw [Glue.sumInt_mul_left, ← dual_sim m l]
    exact congrArg _ (Glue.sumInt_congr (fun k => Int.mul_comm _ _))
  rw [Glue.sumInt_congr h3]
  have h4 : ∀ l : Fin 8, y l * (if m = l then (4 : Int) else 0)
      = if m = l then 4 * y l else 0 := by
    intro l
    refine Decidable.byCases (p := m = l) (fun h => ?_) (fun h => ?_)
    · rw [if_pos h, if_pos h, Int.mul_comm]
    · rw [if_neg h, if_neg h, Int.mul_zero]
  rw [Glue.sumInt_congr h4, sumInt_ite_eq m (fun l => 4 * y l)]

public theorem indep (c : Vec 8 Int)
    (h : ∀ m : Fin 8, Vec.sumInt (fun i => c i * Roots.D19a i m) = 0) (j : Fin 8) : c j = 0 := by
  have key : Vec.sumInt (fun m => Vec.sumInt (fun i => c i * Roots.D19a i m) * dualBasis m j)
      = c j * 4 := by
    have e1 : ∀ m : Fin 8, Vec.sumInt (fun i => c i * Roots.D19a i m) * dualBasis m j
        = Vec.sumInt (fun i => c i * (Roots.D19a i m * dualBasis m j)) := by
      intro m
      rw [← sumInt_mul_right]
      exact Glue.sumInt_congr (fun i => Int.mul_assoc _ _ _)
    rw [Glue.sumInt_congr e1,
      sumInt_exchange (fun m i => c i * (Roots.D19a i m * dualBasis m j))]
    have e2 : ∀ i : Fin 8, Vec.sumInt (fun m => c i * (Roots.D19a i m * dualBasis m j))
        = if j = i then c i * 4 else 0 := by
      intro i
      rw [Glue.sumInt_mul_left, sim_dual i j]
      refine Decidable.byCases (p := j = i) (fun hh => ?_) (fun hh => ?_)
      · rw [if_pos hh, if_pos hh]
      · rw [if_neg hh, if_neg hh, Int.mul_zero]
    rw [Glue.sumInt_congr e2, sumInt_ite_eq j (fun i => c i * 4)]
  rw [Glue.sumInt_congr (fun m => by rw [h m, Int.zero_mul]),
    Glue.sumInt_const] at key
  omega

/-- `V65c`. `Sim` is a `Z`-basis of `L`: the eight simple roots lie in `L`,
every element of `L` is an integer combination of them, and no nonzero integer
combination vanishes. -/
public theorem V65c :
    (∀ i : Fin 8, Glue.MemL 8 (Roots.D19a i))
      ∧ (∀ y : Vec 8 Int, Glue.MemL 8 y →
          ∀ m : Fin 8, y m = Vec.sumInt (fun i => simCoord y i * Roots.D19a i m))
      ∧ (∀ c : Vec 8 Int,
          (∀ m : Fin 8, Vec.sumInt (fun i => c i * Roots.D19a i m) = 0) →
          ∀ i : Fin 8, c i = 0) :=
  ⟨simMemL, fun _ hy => recon hy, indep⟩

/-! ## Places

A `Place` is the ring data section 13 localises along, and nothing more: local
integers inside an ambient ring, the two structure maps out of `Z` and `Q`, and
the one property that makes the ring *a place* rather than an arbitrary
`Z`-algebra --- a rational whose denominator misses the residue characteristic
is already a local integer. That last field is what `RP1` runs on. -/

@[expose] public def homComp {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] (g : RingHom S T) (f : RingHom R S) : RingHom R T where
  toFun r := g.toFun (f.toFun r)
  map_one := by rw [f.map_one, g.map_one]
  map_add a b := by rw [f.map_add, g.map_add]
  map_mul a b := by rw [f.map_mul, g.map_mul]

@[expose] public def homId {R : Type u} [CommRing R] : RingHom R R where
  toFun r := r
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

/-- `D34`. `V = L (x)_Z Q`, the single rational carrier, written in the
coordinates of the `V65c` basis: `Sim` is a `Z`-basis of `L`, so in those
coordinates `L` is `Z^8` and `V` is `Q^8`. `FR1` is the statement that this
really is the tensor product -- every element has a finite-denominator form
`y/m` with `y` integral -- and is proved in `UorAtlas.Prelude.RingLemmas`. -/
public abbrev D34 : Type := Vec 8 Rat

/-- A place of `Q` as section 13 uses one: the local integers `Z_v`, the
ambient `Q_v`, and the structure maps. The two rings are parameters, which is
the whole design: `BC1` and `SD1` need nothing else, so no completion is
constructed. -/
public structure Place where
  Loc : Type
  Amb : Type
  [locRing : CommRing Loc]
  [ambRing : CommRing Amb]
  /-- `Z_v -> Q_v`. -/
  incl : RingHom Loc Amb
  /-- `Z -> Z_v`: the lattice `L` of `D10` enters the local ring along this. -/
  fromInt : RingHom Int Loc
  /-- `iota_v : Q -> Q_v` of section 0. -/
  fromRat : RingHom Rat Amb
  /-- The residue characteristic. -/
  res : Nat
  /-- The square of structure maps commutes: localising an integer through
  `Z_v` and through `Q` agree. -/
  compat : ∀ n : Int,
    incl.toFun (fromInt.toFun n) = fromRat.toFun (NumInstances.intToRat.toFun n)
  /-- What makes this a *place*: a rational integral at `res` lands in `Z_v`.
  At `Z_(p) ⊂ Q` and at `Z_p ⊂ Q_p` alike this is true by definition of the
  local ring, and it is the only property of a place `RP1` consumes. -/
  integral : ∀ q : Rat, IntegralAt res q → InImage incl (fromRat.toFun q)

attribute [instance] Place.locRing Place.ambRing

/-- `Z -> Q_v`, the composite. -/
@[expose] public def Place.fromIntAmb (p : Place) : RingHom Int p.Amb :=
  homComp p.incl p.fromInt

/-- `D35`. `V_v = V (x)_Q Q_v`: extension of scalars along `iota_v`, read one
coordinate at a time. -/
@[expose] public def D35 (p : Place) (x : D34) : Vec 8 p.Amb := Vec.map p.fromRat x

/-- `D35a`. The localised form `<-,->_v` is the scalar extension of the
rational one. -/
public theorem D35a (p : Place) (x y : D34) :
    p.fromRat.toFun (Vec.inner x y) = Vec.inner (D35 p x) (D35 p y) :=
  Vec.inner_map p.fromRat x y

/-- `Gram(Sim)` over the local integers. -/
@[expose] public def gramAt (p : Place) : Mat 8 8 p.Loc := Mat.map p.fromInt Roots.gram

/-- `L_v`: the local lattice, the coordinate vectors with entries in `Z_v`.
`V65c` is what makes this the localisation of `L` rather than of some other
lattice. -/
@[expose] public def locL (p : Place) (c : Vec 8 p.Amb) : Prop := InLattice p.incl c

/-- `D37`. `L_v* := { y in V_v : <y,x>_v in Z_v for all x in L_v }`. -/
@[expose] public def D37 (p : Place) (c : Vec 8 p.Amb) : Prop := InDual p.incl (gramAt p) c

/-- An integer matrix with an integer inverse stays invertible over the local
ring. This is `BC1` at the place, and it is the step that puts the integral
action of `D21` inside `GL_8(Z_v)`. It is not yet `V72`: being invertible over
`Z_v` is the *reason* the lattice is preserved, not the statement that it is. -/
public theorem localInGL (p : Place) {G : Mat 8 8 Int} (hG : InGL G) :
    InGL (Mat.map p.fromInt G) := BC1 p.fromInt hG

/-- A matrix with entries in `Z_v` carries `L_v` into `L_v`: every coordinate of
the image is a sum of products of local integers, and the image of a ring
homomorphism is closed under both. -/
public theorem locL_apply (p : Place) (A : Mat 8 8 p.Loc) {c : Vec 8 p.Amb}
    (hc : locL p c) : locL p (Mat.apply (Mat.map p.incl A) c) :=
  fun i => InImage.sum p.incl _ (fun j => InImage.mul ⟨A i j, rfl⟩ (hc j))

/-- Base change to `Q_v` factors through `Z_v`, because `Z -> Q_v` is by
definition `Z -> Z_v -> Q_v`. -/
public theorem map_fromIntAmb (p : Place) (G : Mat 8 8 Int) :
    Mat.map p.fromIntAmb G = Mat.map p.incl (Mat.map p.fromInt G) := rfl

/-- `V72`. Every `g` in the integral action preserves `L_v`. The matrix carries
the lattice into itself because its entries are local integers, and its inverse
-- which `BC1` supplies through `localInGL` -- carries it back, so the
containment is an equality rather than merely an inclusion. -/
public theorem V72 (p : Place) {G : Mat 8 8 Int} (hG : InGL G) :
    (∀ c : Vec 8 p.Amb, locL p c → locL p (Mat.apply (Mat.map p.fromIntAmb G) c))
      ∧ (∀ c : Vec 8 p.Amb, locL p c →
          ∃ d : Vec 8 p.Amb, locL p d ∧ Mat.apply (Mat.map p.fromIntAmb G) d = c) := by
  obtain ⟨H, hGH, _⟩ := hG
  refine ⟨fun c hc => map_fromIntAmb p G ▸ locL_apply p (Mat.map p.fromInt G) hc,
    fun c hc => ⟨Mat.apply (Mat.map p.fromIntAmb H) c, ?_, ?_⟩⟩
  · exact map_fromIntAmb p H ▸ locL_apply p (Mat.map p.fromInt H) hc
  · have hmap : Mat.mul (Mat.map p.fromIntAmb G) (Mat.map p.fromIntAmb H)
        = (Mat.id : Mat 8 8 p.Amb) := by
      funext i j
      rw [← Mat.map_mul_apply, hGH]
      exact congrFun (congrFun (map_id p.fromIntAmb) i) j
    rw [← Mat.apply_mul, hmap, Mat.apply_id]

public theorem gramAt_InGL (p : Place) : InGL (gramAt p) := localInGL p gram_InGL

/-- `V69`. `L_v` is self-dual, at every place. `SD1` supplies the argument and
`T58x` -- through `gram_InGL` and `BC1` -- supplies its hypothesis. -/
public theorem V69 (p : Place) (c : Vec 8 p.Amb) : D37 p c ↔ locL p c :=
  SD1 p.incl (gramAt_InGL p) c

/-- The localisation of a lattice vector is a local lattice vector. -/
public theorem locL_of_int (p : Place) (x : Vec 8 Int) :
    locL p (Vec.map p.fromIntAmb x) := fun i => ⟨p.fromInt.toFun (x i), rfl⟩

/-- `V74`. Localising commutes with the linear action: applying `g` and then
localising is applying `g_v` to the localised vector. -/
public theorem V74 (p : Place) (G : Mat 8 8 Rat) (x : D34) (i : Fin 8) :
    p.fromRat.toFun (Mat.apply G x i) = Mat.apply (Mat.map p.fromRat G) (D35 p x) i :=
  RH1_apply p.fromRat G x i

/-- `V74` for an integral matrix acting on the lattice, which is the shape the
group layer uses. -/
public theorem V74_int (p : Place) (G : Mat 8 8 Int) (x : Vec 8 Int) (i : Fin 8) :
    p.fromIntAmb.toFun (Mat.apply G x i)
      = Mat.apply (Mat.map p.fromIntAmb G) (Vec.map p.fromIntAmb x) i :=
  RH1_apply p.fromIntAmb G x i

/-! ## The finite places exist: `Z_(p)`

Everything above is parametric, so it is worth nothing until something
satisfies it. `Z_(p)` does, at every prime, and is a subring of `Q` rather than
a completion --- exactly the object section 19.6's `LI1` already describes,
"membership in the localization `Z_(p)`, and hence in `Z_p` after completion,
without either ring being constructed". -/

/-- Euclid's lemma, from the section-0 definition of `Prime`. The prelude has
no `Nat.Prime`, so the step "`p | ab` implies `p | a` or `p | b`" is proved
from the divisor characterisation and `Nat.Coprime`. -/
public theorem IsPrime.dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  refine Decidable.byCases (p := p ∣ a) (fun ha => Or.inl ha) (fun ha => Or.inr ?_)
  have hg : Nat.Coprime p a := by
    rcases hp.2 (Nat.gcd p a) (Nat.gcd_dvd_left p a) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ Nat.gcd_dvd_right p a) ha
  exact hg.dvd_of_dvd_mul_left h

public theorem natAbs_den_mul (a b : Rat) :
    (((a.den : Int) * (b.den : Int) : Int)).natAbs = a.den * b.den := by
  rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]

/-- The reduced denominator of a sum divides the product of the denominators.
`den_dvd_of_scale` of `UorAtlas.Prelude.RingLemmas` does the work; all that is
needed here is the integer the common denominator clears the sum to. -/
public theorem den_add_dvd (a b : Rat) : (a + b).den ∣ a.den * b.den := by
  have hA := den_mul_eq_num a
  have hB := den_mul_eq_num b
  have key : (((a.den : Int) * (b.den : Int) : Int) : Rat) * (a + b)
      = (((b.den : Int) * a.num + (a.den : Int) * b.num : Int) : Rat) := by
    rw [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_mul]
    calc ((a.den : Int) : Rat) * ((b.den : Int) : Rat) * (a + b)
        = ((a.den : Int) : Rat) * ((b.den : Int) : Rat) * a
          + ((a.den : Int) : Rat) * ((b.den : Int) : Rat) * b := Rat.mul_add _ _ _
      _ = ((b.den : Int) : Rat) * (((a.den : Int) : Rat) * a)
          + ((a.den : Int) : Rat) * (((b.den : Int) : Rat) * b) := by
            rw [Rat.mul_comm (((a.den : Int) : Rat)) (((b.den : Int) : Rat)),
              Rat.mul_assoc, Rat.mul_comm (((b.den : Int) : Rat)) (((a.den : Int) : Rat)),
              Rat.mul_assoc]
      _ = ((b.den : Int) : Rat) * (a.num : Rat)
          + ((a.den : Int) : Rat) * (b.num : Rat) := by rw [hA, hB]
  have h := den_dvd_of_scale key
  rwa [natAbs_den_mul] at h

public theorem den_mul_dvd (a b : Rat) : (a * b).den ∣ a.den * b.den := by
  have hA := den_mul_eq_num a
  have hB := den_mul_eq_num b
  have key : (((a.den : Int) * (b.den : Int) : Int) : Rat) * (a * b)
      = ((a.num * b.num : Int) : Rat) := by
    rw [Rat.intCast_mul, Rat.intCast_mul]
    calc ((a.den : Int) : Rat) * ((b.den : Int) : Rat) * (a * b)
        = ((a.den : Int) : Rat) * (((b.den : Int) : Rat) * (a * b)) := Rat.mul_assoc _ _ _
      _ = ((a.den : Int) : Rat) * ((((b.den : Int) : Rat) * a) * b) := by rw [Rat.mul_assoc]
      _ = ((a.den : Int) : Rat) * ((a * ((b.den : Int) : Rat)) * b) := by
            rw [Rat.mul_comm (((b.den : Int) : Rat)) a]
      _ = ((a.den : Int) : Rat) * (a * (((b.den : Int) : Rat) * b)) := by rw [Rat.mul_assoc]
      _ = (((a.den : Int) : Rat) * a) * (((b.den : Int) : Rat) * b) :=
            (Rat.mul_assoc _ _ _).symm
      _ = (a.num : Rat) * (b.num : Rat) := by rw [hA, hB]
  have h := den_dvd_of_scale key
  rwa [natAbs_den_mul] at h

public theorem not_dvd_one {p : Nat} (hp : IsPrime p) : ¬ (p ∣ 1) := by
  intro h
  have h1 := Nat.le_of_dvd (by decide) h
  have h2 := hp.1
  omega

public theorem integralAt_intCast {p : Nat} (hp : IsPrime p) (n : Int) :
    IntegralAt p ((n : Int) : Rat) := by
  show ¬ (p ∣ (((n : Int) : Rat)).den)
  rw [Rat.den_intCast]
  exact not_dvd_one hp

public theorem integralAt_zero {p : Nat} (hp : IsPrime p) : IntegralAt p 0 :=
  not_dvd_one hp

public theorem integralAt_one {p : Nat} (hp : IsPrime p) : IntegralAt p 1 :=
  not_dvd_one hp

public theorem integralAt_neg {p : Nat} {a : Rat} (h : IntegralAt p a) :
    IntegralAt p (-a) := by
  show ¬ (p ∣ (-a).den)
  rw [Rat.neg_den]
  exact h

public theorem integralAt_add {p : Nat} (hp : IsPrime p) {a b : Rat}
    (ha : IntegralAt p a) (hb : IntegralAt p b) : IntegralAt p (a + b) := by
  intro hd
  rcases IsPrime.dvd_mul hp (Nat.dvd_trans hd (den_add_dvd a b)) with h | h
  · exact ha h
  · exact hb h

public theorem integralAt_mul {p : Nat} (hp : IsPrime p) {a b : Rat}
    (ha : IntegralAt p a) (hb : IntegralAt p b) : IntegralAt p (a * b) := by
  intro hd
  rcases IsPrime.dvd_mul hp (Nat.dvd_trans hd (den_mul_dvd a b)) with h | h
  · exact ha h
  · exact hb h

/-- The finite places of `Q`: the primes. -/
public abbrev Pl : Type := { n : Nat // IsPrime n }

/-- `Z_(p)`: the rationals integral at `p`. A genuine subring of `Q` --- the
closure proofs above are Euclid's lemma applied to the reduced denominators. -/
@[expose] public def Zloc (p : Pl) : Type := { q : Rat // IntegralAt p.val q }

public instance instAddCommGroupZloc (p : Pl) : AddCommGroup (Zloc p) where
  zero := ⟨0, integralAt_zero p.2⟩
  add x y := ⟨x.val + y.val, integralAt_add p.2 x.2 y.2⟩
  neg x := ⟨-x.val, integralAt_neg x.2⟩
  add_assoc _ _ _ := Subtype.ext (Rat.add_assoc _ _ _)
  add_comm _ _ := Subtype.ext (Rat.add_comm _ _)
  add_zero _ := Subtype.ext (Rat.add_zero _)
  add_neg _ := Subtype.ext (Rat.add_neg_cancel _)

public instance instCommRingZloc (p : Pl) : CommRing (Zloc p) where
  toAddCommGroup := instAddCommGroupZloc p
  one := ⟨1, integralAt_one p.2⟩
  mul x y := ⟨x.val * y.val, integralAt_mul p.2 x.2 y.2⟩
  mul_assoc _ _ _ := Subtype.ext (Rat.mul_assoc _ _ _)
  mul_comm _ _ := Subtype.ext (Rat.mul_comm _ _)
  one_mul _ := Subtype.ext (Rat.one_mul _)
  left_distrib _ _ _ := Subtype.ext (Rat.mul_add _ _ _)

/-- `Z_(p) -> Q`. -/
@[expose] public def ZlocIncl (p : Pl) : RingHom (Zloc p) Rat where
  toFun x := x.val
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

/-- `Z -> Z_(p)`. -/
@[expose] public def ZlocFromInt (p : Pl) : RingHom Int (Zloc p) where
  toFun n := ⟨(n : Rat), integralAt_intCast p.2 n⟩
  map_one := rfl
  map_add a b := Subtype.ext (Rat.intCast_add a b)
  map_mul a b := Subtype.ext (Rat.intCast_mul a b)

/-- The place at `p`: `Z_(p)` inside `Q`. This is what makes every statement
above non-vacuous, at every prime. -/
@[expose] public def placeAt (p : Pl) : Place where
  Loc := Zloc p
  Amb := Rat
  incl := ZlocIncl p
  fromInt := ZlocFromInt p
  fromRat := homId
  res := p.val
  compat _ := rfl
  integral q hq := ⟨⟨q, hq⟩, rfl⟩

/-! ## `Addr(L)`, `RP1`, and the diagonal coupling -/

/-- A system of finite places: one place per prime, its residue characteristic
being that prime. -/
public structure PlaceSystem where
  at_ : Pl → Place
  res_eq : ∀ p : Pl, (at_ p).res = p.val

/-- The system of localizations. The restricted product below is therefore a
statement about an inhabited index of genuine rings. -/
@[expose] public def locSystem : PlaceSystem where
  at_ := placeAt
  res_eq _ := rfl

/-- `D38`. `Addr(L)`, the restricted product of the local spaces `V_v` with
respect to the local lattices `L_v`: a family of local vectors that is integral
at all but finitely many places.

"Finitely many" is containment in a list. That is the only notion of finite
subset available without `Finset`, and it is the one the document's own
bad-denominator argument produces, since that argument *enumerates* the
exceptional places. -/
public structure D38 (S : PlaceSystem) where
  comp : (p : Pl) → Vec 8 (S.at_ p).Amb
  ae : ∃ l : List Nat, ∀ p : Pl, p.val ∉ l → InLattice (S.at_ p).incl (comp p)

/-- Two addresses agreeing at every place are equal: the almost-everywhere
condition is a proposition, so it carries no data to disagree about. -/
public theorem D38.ext {S : PlaceSystem} {a b : D38 S} (h : ∀ p, a.comp p = b.comp p) :
    a = b := by
  obtain ⟨ca, _⟩ := a
  obtain ⟨cb, _⟩ := b
  have hc : ca = cb := funext h
  subst hc
  rfl

public theorem inImage_neg {A : Type u} {F : Type v} [CommRing A] [CommRing F]
    {φ : RingHom A F} {t : F} (h : InImage φ t) : InImage φ (AddCommGroup.neg t) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨AddCommGroup.neg a, by rw [ha, NumInstances.ringHom_map_neg]⟩

public instance instAddCommGroupD38 (S : PlaceSystem) : AddCommGroup (D38 S) where
  zero :=
    { comp := fun _ => AddCommGroup.zero
      ae := ⟨[], fun p _ i => by
        rw [Vec.zero_apply]
        exact InImage.zero (S.at_ p).incl⟩ }
  add a b :=
    { comp := fun p => AddCommGroup.add (a.comp p) (b.comp p)
      ae := by
        obtain ⟨la, ha⟩ := a.ae
        obtain ⟨lb, hb⟩ := b.ae
        refine ⟨la ++ lb, fun p hp i => ?_⟩
        rw [Vec.add_apply]
        exact InImage.add (ha p (fun h => hp (List.mem_append.mpr (Or.inl h))) i)
          (hb p (fun h => hp (List.mem_append.mpr (Or.inr h))) i) }
  neg a :=
    { comp := fun p => AddCommGroup.neg (a.comp p)
      ae := by
        obtain ⟨la, ha⟩ := a.ae
        refine ⟨la, fun p hp i => ?_⟩
        rw [Vec.neg_apply]
        exact inImage_neg (ha p hp i) }
  add_assoc _ _ _ := D38.ext (fun _ => AddCommGroup.add_assoc _ _ _)
  add_comm _ _ := D38.ext (fun _ => AddCommGroup.add_comm _ _)
  add_zero _ := D38.ext (fun _ => AddCommGroup.add_zero _)
  add_neg _ := D38.ext (fun _ => AddCommGroup.add_neg _)

public theorem D38.add_comp {S : PlaceSystem} (a b : D38 S) (p : Pl) (i : Fin 8) :
    (AddCommGroup.add a b).comp p i = AddCommGroup.add (a.comp p i) (b.comp p i) := rfl

public theorem D38.neg_comp {S : PlaceSystem} (a : D38 S) (p : Pl) (i : Fin 8) :
    (AddCommGroup.neg a).comp p i = AddCommGroup.neg (a.comp p i) := rfl

/-- Scaling an address by a rational. The definition *is* the content of `RP1`:
the almost-everywhere condition survives, because the primes at which `q` fails
to be a local integer are the primes dividing its denominator, and `DV1` says
those are finitely many. -/
@[expose] public def ratSmul {S : PlaceSystem} (q : Rat) (a : D38 S) : D38 S where
  comp p := Vec.smul ((S.at_ p).fromRat.toFun q) (a.comp p)
  ae := by
    obtain ⟨l, hl⟩ := a.ae
    have hden : ((q.den : Int)) ≠ 0 := by
      have h := q.den_nz
      omega
    obtain ⟨lq, hq⟩ := DV1 hden
    refine ⟨l ++ lq, fun p hp i => ?_⟩
    have hint : IntegralAt (S.at_ p).res q := by
      rw [S.res_eq p]
      intro hdvd
      exact hp (List.mem_append.mpr (Or.inr
        (hq p.val ⟨p.2, Int.natCast_dvd_natCast.mpr hdvd⟩)))
    exact InImage.mul ((S.at_ p).integral q hint)
      (hl p (fun h => hp (List.mem_append.mpr (Or.inl h))) i)

public theorem ratSmul_comp {S : PlaceSystem} (q : Rat) (a : D38 S) (p : Pl) (i : Fin 8) :
    (ratSmul q a).comp p i = CommRing.mul ((S.at_ p).fromRat.toFun q) (a.comp p i) := rfl

/-- `RP1` (section 19.6). `Addr(L)` carries its canonical `Q`-module structure.

The reason it does is `DV1`: a rational has finitely many denominator primes,
so scaling moves the exceptional set by a finite amount and an address stays an
address. That is discharged in `ratSmul` itself; what remains, and is stated
here, is that the resulting operation satisfies the module laws. -/
public theorem RP1 (S : PlaceSystem) :
    (∀ a : D38 S, ratSmul 1 a = a)
      ∧ (∀ (q r : Rat) (a : D38 S), ratSmul (q * r) a = ratSmul q (ratSmul r a))
      ∧ (∀ (q r : Rat) (a : D38 S), ratSmul (q + r) a
          = AddCommGroup.add (ratSmul q a) (ratSmul r a))
      ∧ (∀ (q : Rat) (a b : D38 S), ratSmul q (AddCommGroup.add a b)
          = AddCommGroup.add (ratSmul q a) (ratSmul q b)) := by
  refine ⟨fun a => D38.ext (fun p => funext (fun i => ?_)),
    fun q r a => D38.ext (fun p => funext (fun i => ?_)),
    fun q r a => D38.ext (fun p => funext (fun i => ?_)),
    fun q a b => D38.ext (fun p => funext (fun i => ?_))⟩
  · have h : (S.at_ p).fromRat.toFun 1 = CommRing.one := (S.at_ p).fromRat.map_one
    rw [ratSmul_comp, h, CommRing.one_mul]
  · have h : (S.at_ p).fromRat.toFun (q * r)
        = CommRing.mul ((S.at_ p).fromRat.toFun q) ((S.at_ p).fromRat.toFun r) :=
      (S.at_ p).fromRat.map_mul q r
    rw [ratSmul_comp, ratSmul_comp, ratSmul_comp, h, CommRing.mul_assoc]
  · have h : (S.at_ p).fromRat.toFun (q + r)
        = AddCommGroup.add ((S.at_ p).fromRat.toFun q) ((S.at_ p).fromRat.toFun r) :=
      (S.at_ p).fromRat.map_add q r
    rw [ratSmul_comp, D38.add_comp, ratSmul_comp, ratSmul_comp, h, Linear.right_distrib]
  · rw [ratSmul_comp, D38.add_comp, D38.add_comp, ratSmul_comp, ratSmul_comp,
      CommRing.left_distrib]

/-- `V70`. The bad-denominator set of a rational vector is finite: outside
finitely many primes, every coordinate is a local integer.

`FR1` clears a common denominator `m`, `DV1` bounds the primes dividing `m`,
and `LI1` says every prime outside that bound leaves the coordinates
integral. -/
public theorem V70 {n : Nat} (x : Vec n Rat) :
    IsFinite (fun p => IsPrime p ∧ ¬ (∀ i : Fin n, IntegralAt p (x i))) := by
  obtain ⟨y, m, hm, hx⟩ := FR1 x
  obtain ⟨l, hl⟩ := DV1 (m := m) (by omega)
  refine ⟨l, fun p hp => hl p ⟨hp.1, ?_⟩⟩
  exact Classical.byContradiction
    (fun hnd => hp.2 (fun i => LI1 (by omega) (hx i) hnd))

/-- `V70` in the form the diagonal embedding consumes. -/
public theorem integral_off {n : Nat} (x : Vec n Rat) :
    ∃ l : List Nat, ∀ p : Nat, IsPrime p → p ∉ l → ∀ i : Fin n, IntegralAt p (x i) := by
  obtain ⟨l, hl⟩ := V70 x
  exact ⟨l, fun p hp hnp => Classical.byContradiction (fun h => hnp (hl p ⟨hp, h⟩))⟩

/-- The diagonal embedding `V -> Addr(L)`: one rational vector, localised at
every place at once. `V70` is exactly what makes it land in the restricted
product, and this is the coupling section 13 is named for. -/
@[expose] public def diag {S : PlaceSystem} (x : D34) : D38 S where
  comp p := D35 (S.at_ p) x
  ae := by
    obtain ⟨l, hl⟩ := integral_off x
    exact ⟨l, fun p hp i => (S.at_ p).integral (x i)
      (by rw [S.res_eq p]; exact hl p.val p.2 hp i)⟩

public theorem diag_comp {S : PlaceSystem} (x : D34) (p : Pl) (i : Fin 8) :
    (diag (S := S) x).comp p i = (S.at_ p).fromRat.toFun (x i) := rfl

/-- `D44`. `PAddr(L) = Addr(L)/{+1,-1}_diag`: a single global sign, not one per
place. `signAct` of `UorAtlas.Prelude.RingLemmas` is that diagonal action. -/
public abbrev D44 (S : PlaceSystem) : Type :=
  Quot (OrbitRel (signAct : Bool → D38 S → D38 S))

/-- Localising commutes with negation: the equivariance hypothesis of `QL1` at
the diagonal sign action. -/
public theorem diag_neg {S : PlaceSystem} (z : D34) :
    diag (S := S) (AddCommGroup.neg z) = AddCommGroup.neg (diag (S := S) z) :=
  D38.ext (fun p => funext (fun i => by
    rw [diag_comp, Vec.neg_apply, NumInstances.ringHom_map_neg, D38.neg_comp,
      diag_comp]))

/-- The diagonal embedding descends to the sign quotients. This is `QL1` at the
diagonal sign action. -/
public theorem diag_sign {S : PlaceSystem} {x y : D34}
    (h : OrbitRel signAct x y) :
    OrbitRel signAct (diag (S := S) x) (diag (S := S) y) :=
  QL1_sign diag diag_neg h

/-- `PAddr(L)` as the codomain of the descended diagonal map. -/
@[expose] public def diagP {S : PlaceSystem} : Quot (OrbitRel (signAct : Bool → D34 → D34))
    → D44 S :=
  QL1.descend signAct signAct diag
    (fun g z => by cases g with
      | true => exact diag_neg z
      | false => rfl)

end UorAtlas.Places
