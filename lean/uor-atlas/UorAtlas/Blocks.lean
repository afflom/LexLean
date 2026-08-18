module
public import Init
public import UorAtlas.Prelude.Algebra
public import UorAtlas.Prelude.NumInstances
public import UorAtlas.Prelude.Linear
public import UorAtlas.Prelude.Bitset
public import UorAtlas.Glue
public import UorAtlas.Roots

/-!
Sections 3, 4 and 6 of `UOR-ATLAS-FORMAL-001`: the bound `D14`-`D15`, the
Atlas layer `D16`-`D19`, `D22`, `D22a`, `D46a`, and the theorems `T10a`-`T10c`,
`T11`-`T19`, `T16x`, `T61a`.

## What is proved and what is not

`T22`, `T23` and `T24` -- the counts `|Blk| = 3150`, `|Frm| = 1575`,
`|Atl| = 75600` -- are **not** in this module, and neither are the statements
that quantify over the whole census (`T20`, `T20a`, `T21`, `T25`, `T25x`,
`T26`, `T26x`, `T26a`, `T26b`, `T22a`). The reason is stated once here rather
than repeated: a census needs a *completeness* proof, and the cheapest complete
enumeration of `D16` blocks runs over the `C(120,4) = 8214570` four-element
subsets of `K`, because `rank_Q = 4` gives a spanning four-subset and nothing
smaller determines the span. Each subset costs a `4 x 4` Gram determinant and,
when that is nonzero, a `120`-class span scan. That is upwards of `10^9` kernel
reductions, three orders of magnitude beyond what `decide +kernel` completes
here, and every cheaper enumeration this module could run -- over orthogonal
four-cliques, say -- is complete only modulo the classification of rank-`4`
root systems, which is not available without a real linear-algebra library.
Asserting the counts on the strength of an incomplete enumeration would be the
one thing this repository exists not to do.

Everything below is therefore either a general theorem about all
AtlasPresentations (`T12`, `T13`), a general theorem about all class subsets
(`T10a`, `T10c`), or a verified statement about the exhibited witness, which is
exactly the scope the document gives `T11` and `T14`-`T19`.

## Coordinates

The 2x integer scaling of `UorAtlas.Roots` is in force: a class is an element
of `K = Fin 120`, its representative root `rep i` has `<y,y> = 8`, and
adjacency `D13` is `|<u,v>| = 4`. `Rat` appears in exactly two places, both of
which the document asks for: `D19`'s matrix of *rational averages*, and the
`Q`-span of `D16`'s rank condition.

## Class subsets

A subset of `K` is a `Bitset`, the `Nat`-backed finite set of
`UorAtlas.Prelude.Bitset`. Blocks and AtlasInstances are written as single
numerals, so a membership test is one machine `testBit` and a cardinality one
popcount rather than a list traversal.
-/

set_option autoImplicit false
set_option maxRecDepth 40000

namespace UorAtlas.Blocks

open UorAtlas.Prelude
open UorAtlas.Prelude.AddCommGroup
open UorAtlas.Prelude.CommRing
open UorAtlas.Prelude.Linear
open UorAtlas.Prelude.NumInstances
open UorAtlas.Roots

/-! ## The `Q`-span, for `D16`'s rank condition

`D16` asks for `rank_Q` of a set of integer vectors, so the span has to be
taken over `Q` and not over `Z`. The two lemmas at the end of this section are
the only ones the rest of the module uses, and both of them reduce a rational
statement to an integer computation: `indep_of_orth` gets independence from
pairwise orthogonality, and `inSpan_of_recon` gets span membership from the
integer reconstruction identity `8 v = sum_i <v,b_i> b_i`, which is what an
orthogonal basis of norm `8` makes exact over `Z`.
-/

/-- Extension of scalars `Z -> Q` on a vector: `V = L (x)_Z Q` of `D34`, read
one vector at a time. -/
@[expose] public def qOf (x : Vec 8 Int) : Vec 8 Rat := Vec.map intToRat x

/-- The rational linear combination `sum_i c_i b_i` of `k` integer vectors. -/
@[expose] public def qComb {k : Nat} (b : Fin k → Vec 8 Int) (c : Vec k Rat) : Vec 8 Rat :=
  fun j => Vec.sum (fun i => mul (c i) (qOf (b i) j))

/-- `v` lies in the `Q`-span of `b`. -/
@[expose] public def InSpan {k : Nat} (b : Fin k → Vec 8 Int) (v : Vec 8 Rat) : Prop :=
  ∃ c : Vec k Rat, ∀ j : Fin 8, v j = qComb b c j

/-- `b` is `Q`-linearly independent. -/
@[expose] public def Indep {k : Nat} (b : Fin k → Vec 8 Int) : Prop :=
  ∀ c : Vec k Rat, (∀ j : Fin 8, qComb b c j = 0) → ∀ i : Fin k, c i = 0

/-- `rank_Q S = r`: some `r` vectors of `S` are `Q`-independent and span `S`.
This is the dimension of the `Q`-span of `S`, presented by a basis drawn from
`S` itself -- the standard characterisation, and the one a witness can
discharge. -/
@[expose] public def HasRank (S : Vec 8 Int → Prop) (r : Nat) : Prop :=
  ∃ b : Fin r → Vec 8 Int, (∀ i : Fin r, S (b i)) ∧ Indep b ∧ ∀ x, S x → InSpan b (qOf x)

/-- The bilinear form is linear in a rational combination. This is `M4` and
`sum_exchange` specialised to the shape `qComb` has. -/
public theorem inner_qComb {k : Nat} (b : Fin k → Vec 8 Int) (c : Vec k Rat) (y : Vec 8 Rat) :
    Vec.inner (qComb b c) y = Vec.sum (fun i => mul (c i) (Vec.inner (qOf (b i)) y)) := by
  show Vec.sum (fun j => mul (Vec.sum (fun i => mul (c i) (qOf (b i) j))) (y j)) = _
  have h1 : ∀ j : Fin 8, mul (Vec.sum (fun i => mul (c i) (qOf (b i) j))) (y j)
      = Vec.sum (fun i => mul (c i) (mul (qOf (b i) j) (y j))) := by
    intro j
    rw [Vec.sum_mul]
    exact Vec.sum_congr (fun i => mul_assoc (c i) (qOf (b i) j) (y j))
  rw [Vec.sum_congr h1, Vec.sum_exchange (fun j i => mul (c i) (mul (qOf (b i) j) (y j)))]
  exact Vec.sum_congr (fun i => (Vec.mul_sum (c i) (fun j => mul (qOf (b i) j) (y j))).symm)

/-- `<qOf x, qOf y> = <x,y>` in `Q`: `inner_map` along `Z -> Q`. -/
public theorem inner_qOf (x y : Vec 8 Int) :
    Vec.inner (qOf x) (qOf y) = ((dot x y : Int) : Rat) := by
  rw [dot_eq_inner]
  exact (Vec.inner_map intToRat x y).symm

/-- Pairwise orthogonal integer vectors of norm `8` are `Q`-independent: pair
the vanishing combination with each basis vector and the form reads off the
coefficient. -/
public theorem indep_of_orth {k : Nat} (b : Fin k → Vec 8 Int)
    (h : ∀ i j : Fin k, dot (b i) (b j) = if i = j then 8 else 0) : Indep b := by
  intro c hc i
  have hz : Vec.inner (qComb b c) (qOf (b i)) = (0 : Rat) := by
    have hp : ∀ j : Fin 8, mul (qComb b c j) (qOf (b i) j) = (0 : Rat) := by
      intro j; rw [hc j]; exact zero_mul _
    show Vec.sum (fun j => mul (qComb b c j) (qOf (b i) j)) = (0 : Rat)
    rw [Vec.sum_congr hp]
    exact Vec.sum_zero
  rw [inner_qComb] at hz
  have hterm : ∀ t : Fin k, mul (c t) (Vec.inner (qOf (b t)) (qOf (b i)))
      = (if i = t then mul (c t) 8 else zero) := by
    intro t
    rw [inner_qOf, h t i]
    by_cases ht : t = i
    · rw [if_pos ht, if_pos ht.symm]; rfl
    · rw [if_neg ht, if_neg (fun hh => ht hh.symm)]
      exact mul_zero (c t)
  rw [Vec.sum_congr hterm, Vec.sum_ite_eq i (fun t => mul (c t) 8)] at hz
  have hz2 : c i * 8 = 0 := hz
  have hone : (8 : Rat) * (8 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 8 (by decide)
  have h2 : c i * 8 * (8 : Rat)⁻¹ = c i := by rw [Rat.mul_assoc, hone, Rat.mul_one]
  have hzm : (0 : Rat) * (8 : Rat)⁻¹ = 0 := zero_mul _
  rw [← h2, hz2, hzm]

/-- The reconstruction identity `8 v = sum_i <v,b_i> b_i` puts `v` in the
`Q`-span of `b` with coefficients `<v,b_i> / 8`. Over `Z` the identity is a
finite check; the division by `8` happens once, in `Q`. -/
public theorem inSpan_of_recon {k : Nat} (b : Fin k → Vec 8 Int) (v : Vec 8 Int)
    (h : ∀ j : Fin 8, 8 * v j = Vec.sumInt (fun i => dot v (b i) * b i j)) :
    InSpan b (qOf v) := by
  refine ⟨fun i => (8 : Rat)⁻¹ * ((dot v (b i) : Int) : Rat), fun j => ?_⟩
  show ((v j : Int) : Rat) = Vec.sum (fun i =>
    mul ((8 : Rat)⁻¹ * ((dot v (b i) : Int) : Rat)) ((b i j : Int) : Rat))
  have hterm : ∀ i : Fin k,
      mul ((8 : Rat)⁻¹ * ((dot v (b i) : Int) : Rat)) ((b i j : Int) : Rat)
        = mul ((8 : Rat)⁻¹) (((dot v (b i) * b i j : Int) : Rat)) := by
    intro i
    rw [Rat.intCast_mul (dot v (b i)) (b i j)]
    exact Rat.mul_assoc _ _ _
  rw [Vec.sum_congr hterm, ← Vec.mul_sum]
  have hcast : Vec.sum (fun i => ((dot v (b i) * b i j : Int) : Rat))
      = ((Vec.sumInt (fun i => dot v (b i) * b i j) : Int) : Rat) := by
    rw [Vec.sumInt_eq_sum]
    exact (hom_map_sum intToRat (fun i => dot v (b i) * b i j)).symm
  rw [hcast, ← h j, Rat.intCast_mul 8 (v j)]
  have h8 : (8 : Rat)⁻¹ * (((8 : Int) : Rat)) = 1 := Rat.inv_mul_cancel 8 (by decide)
  show ((v j : Int) : Rat) = (8 : Rat)⁻¹ * (((8 : Int) : Rat) * ((v j : Int) : Rat))
  rw [← Rat.mul_assoc, h8, Rat.one_mul]

/-! ## Class subsets, and the bridge from `Bitset.card` to a sum over `K`

A subset of `K` is a `Bitset` all of whose bits lie below `120`, which is the
same as the numeral being below `2^120`. `card_eq_sumN` is the one structural
fact the counting theorems need: a popcount is the sum of the `120` indicator
bits, so `T12`'s cardinality and `T13`'s root count speak about the same
number. -/

/-- A `Bitset` presents a subset of `K` exactly when it holds no bit at or
above `120`. -/
@[expose] public def ClassSet (W : Bitset) : Prop := Bitset.toNat W < 2 ^ 120

public instance ClassSet.instDecidable (W : Bitset) : Decidable (ClassSet W) :=
  inferInstanceAs (Decidable (Bitset.toNat W < 2 ^ 120))

public theorem lt_of_mem {W : Bitset} (h : ClassSet W) {i : Nat} (hi : i ∈ W) : i < 120 := by
  rcases Nat.lt_or_ge i 120 with hc | hc
  · exact hc
  · have hlt : Bitset.toNat W < 2 ^ i :=
      Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hc)
    have hfalse : Nat.testBit W i = false := Nat.testBit_lt_two_pow hlt
    rw [(Bitset.mem_def W i).mp hi] at hfalse
    exact absurd hfalse (by decide)

/-- The `0`/`1` indicator of membership, as one named function so that every
counting lemma below uses the same `Decidable` instance. -/
@[expose] public def ind (W : Bitset) (i : Nat) : Nat := if i ∈ W then 1 else 0

public theorem card_split (W : Nat) : ∀ m : Nat,
    Bitset.card W = sumN (fun i => if Nat.testBit W i = true then 1 else 0) m
      + Bitset.card (W / 2 ^ m) := by
  intro m
  induction m with
  | zero => show Bitset.card W = 0 + Bitset.card (W / 1); rw [Nat.div_one]; omega
  | succ n ih =>
    have hstep : Bitset.card (W / 2 ^ n)
        = (W / 2 ^ n) % 2 + Bitset.card (W / 2 ^ n / 2) := Bitset.card_step _
    have hdiv : W / 2 ^ n / 2 = W / 2 ^ (n + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    have hbit : (if Nat.testBit W n = true then 1 else 0) = (W / 2 ^ n) % 2 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hm : (W / 2 ^ n) % 2 = 0 ∨ (W / 2 ^ n) % 2 = 1 := by omega
      rcases hm with h | h <;> rw [h] <;> rfl
    rw [sumN_succ, ih, hstep, hdiv, hbit]
    omega

/-- The popcount of a class subset is the number of classes it holds. -/
public theorem card_eq_sumN {W : Bitset} (h : ClassSet W) :
    Bitset.card W = sumN (ind W) 120 := by
  have hz : Bitset.toNat W / 2 ^ 120 = 0 := Nat.div_eq_of_lt h
  have hs := card_split (Bitset.toNat W) 120
  rw [hz] at hs
  have hc0 : Bitset.card (0 : Nat) = 0 := Bitset.card_empty
  rw [hc0, Nat.add_zero] at hs
  exact hs

/-- The same count as a sum over `K`. -/
public theorem card_eq_sum_fin {W : Bitset} (h : ClassSet W) :
    Vec.sumNat (fun u : K => ind W u.val) = Bitset.card W := by
  rw [card_eq_sumN h]
  exact sumNat_eq_sumN 120 (ind W)

public theorem sumN_congr_lt (f g : Nat → Nat) : ∀ m : Nat, (∀ k, k < m → f k = g k) →
    sumN f m = sumN g m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [sumN_succ, sumN_succ, h n (Nat.lt_succ_self n), ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

public theorem sumN_split (f : Nat → Nat) (m : Nat) : ∀ n : Nat,
    sumN f (m + n) = sumN (fun k => f (k + m)) n + sumN f m := by
  intro n
  induction n with
  | zero => show sumN f m = 0 + sumN f m; omega
  | succ p ih =>
    have hm : m + (p + 1) = (m + p) + 1 := by omega
    have hg : p + m = m + p := by omega
    rw [hm, sumN_succ, ih, sumN_succ]
    show f (m + p) + (sumN (fun k => f (k + m)) p + sumN f m)
      = f (p + m) + sumN (fun k => f (k + m)) p + sumN f m
    rw [hg]
    omega

/-! ## `D14` and `D15`: the degree in a class subset, and tightness -/

/-- `D14`. For `W subset K` and `v in K`, `deg_W(v) := |{u in W : {u,v} in E}|`.
`A u v` is the `0`/`1` indicator of `{u,v} in E` by `A_spec`, so this sum is
that cardinality. -/
@[expose] public def D14 (W : Bitset) (v : K) : Nat :=
  Vec.sumNat (fun u : K => if u.val ∈ W then A u v else 0)

public instance D13.instDecidable (u v : K) : Decidable (D13 u v) :=
  inferInstanceAs (Decidable (u ≠ v ∧ (dot (rep u) (rep v) = 4 ∨ dot (rep u) (rep v) = -4)))

/-- `D14` really is a cardinality: its summand is the indicator of
`{u in W : {u,v} in E}`. -/
public theorem D14_counts (W : Bitset) (v : K) :
    D14 W v = Vec.sumNat (fun u : K => if u.val ∈ W ∧ D13 u v then 1 else 0) := by
  refine Vec.sumNat_congr (fun u => ?_)
  by_cases hu : u.val ∈ W
  · rw [if_pos hu]
    by_cases he : D13 u v
    · rw [if_pos ⟨hu, he⟩]; exact A_of_D13 he
    · rw [if_neg (fun hh => he hh.2)]; exact A_of_not_D13 he
  · rw [if_neg hu, if_neg (fun hh => hu hh.1)]

/-- The same degree over `Nat` indices, which is the form the kernel runs. -/
@[expose] public def degN (W : Bitset) (v : Nat) : Nat :=
  sumN (fun u => if u ∈ W then adjN u v else 0) 120

public theorem D14_eq_degN (W : Bitset) (v : K) : D14 W v = degN W v.val :=
  sumNat_eq_sumN 120 (fun u => if u ∈ W then adjN u v.val else 0)

/-- `D15`. `W` is *tight* iff `deg_W(v) = 20` for all `v in W` and
`deg_W(v) = 24` for all `v not in W`. -/
@[expose] public def D15 (W : Bitset) : Prop :=
  (∀ v : K, v.val ∈ W → D14 W v = 20) ∧ (∀ v : K, v.val ∉ W → D14 W v = 24)

/-- `T10c`. The equality form `A.chi = -4.chi + 24.1` is exactly the tightness
condition. `D60` is the reason this matters: the right-hand side is linear in
the indicator, so tightness is an arithmetic identity rather than a subset
search. -/
public theorem T10c (W : Bitset) :
    (∀ v : K, (D14 W v : Int) = -4 * (if v.val ∈ W then 1 else 0) + 24) ↔ D15 W := by
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have := h v; rw [if_pos hv] at this; omega
    · have := h v; rw [if_neg hv] at this; omega
  · intro h v
    by_cases hv : v.val ∈ W
    · rw [if_pos hv, h.1 v hv]; decide
    · rw [if_neg hv, h.2 v hv]; decide

/-- `T10a`. The Hoffman bound is exactly `20` over `Q`: with `|W| = classes/2 = 48`
and `|K| = 120`, `56*|W|/|K| + (-4)*(1 - |W|/|K|) = 20`. -/
public theorem T10a : (56 : Rat) * (48 / 120) + (-4) * (1 - 48 / 120) = 20 := by
  decide +kernel

/-! ## `D16`: blocks

A block is a `12`-class set of rank `4`. The rank is discharged by an explicit
orthogonal quadruple drawn from the block: four classes of norm `8` that are
pairwise orthogonal are `Q`-independent by `indep_of_orth`, and every root of
the block satisfies the integer reconstruction identity
`8 v = sum_i <v,b_i> b_i` of `inSpan_of_recon`. Both halves are finite integer
checks, which is what keeps `D16` decidable at this scale. -/

/-- The lifted root set of a class subset: `{ x in R : k(x) in B }`. -/
@[expose] public def RootsOf (B : Bitset) (x : Vec 8 Int) : Prop := D11 x ∧ (D12 x).val ∈ B

/-- `D16`. `B subset K` is a *block* iff `|B| = stride / 2` and
`rank_Q { x : k(x) in B } = 4`. `stride = 24` by `T3`, so `|B| = 12`. -/
@[expose] public def D16 (B : Bitset) : Prop :=
  ClassSet B ∧ Bitset.card B = 12 ∧ HasRank (RootsOf B) 4

/-- The integer reconstruction identity that `inSpan_of_recon` consumes. -/
@[expose] public def Recon (b : Fin 4 → Vec 8 Int) (v : Vec 8 Int) : Prop :=
  ∀ j : Fin 8, 8 * v j = Vec.sumInt (fun i : Fin 4 => dot v (b i) * b i j)

/-- Reconstruction passes to the antipode, which is what lets a check over the
`120` class representatives cover all `240` roots. -/
public theorem Recon.neg {b : Fin 4 → Vec 8 Int} {v : Vec 8 Int} (h : Recon b v) :
    Recon b (AddCommGroup.neg v) := by
  intro j
  have hj : (AddCommGroup.neg v : Vec 8 Int) j = -(v j) := rfl
  have hsum : Vec.sumInt (fun i : Fin 4 => dot (AddCommGroup.neg v) (b i) * b i j)
      = Vec.sumInt (fun i : Fin 4 => -(dot v (b i) * b i j)) := by
    refine Glue.sumInt_congr (fun i => ?_)
    rw [dot_neg_left v (b i), Int.neg_mul]
  rw [hj, hsum, sumInt_negate, ← h j, Int.mul_neg]

/-! ### The decidable block certificate

Four class indices are packed one byte each into `tab`. `blockOK` checks, in a
single `Bool`, that `B` is a subset of `K` of size `12`, that the four indices
`tab` names lie in `B`, that their representatives are pairwise orthogonal of
norm `8`, and that every class of `B` reconstructs from them. -/

@[expose] public def byteAt (tab i : Nat) : Nat := (tab >>> (8 * i)) &&& 255

@[expose] public def basisOf (tab : Nat) : Fin 4 → Vec 8 Int := fun i => repN (byteAt tab i.val)

@[expose] public def reconBool (tab c : Nat) : Bool :=
  allFin (fun j : Fin 8 => decide (8 * repN c j
    = Vec.sumInt (fun i : Fin 4 => dot (repN c) (basisOf tab i) * basisOf tab i j)))

@[expose] public def blockOK (tab : Nat) (B : Bitset) : Bool :=
  decide (Bitset.toNat B < 2 ^ 120)
    && decide (Bitset.card B = 12)
    && allFin (fun i : Fin 4 => decide (byteAt tab i.val ∈ B))
    && allFin (fun i : Fin 4 => allFin (fun j : Fin 4 =>
        decide (dot (basisOf tab i) (basisOf tab j) = (if i = j then 8 else 0))))
    && allLt (fun c => !(Bitset.mem B c) || reconBool tab c) 120

public theorem D11_repN {c : Nat} (hc : c < 120) : D11 (repN c) :=
  (isD11_iff _).mp (allLt_true _ _ repIsRoot c hc)

public theorem D12_repN {c : Nat} (hc : c < 120) : (D12 (repN c)).val = c :=
  congrArg Fin.val (D12_rep ⟨c, hc⟩)

/-- A passing certificate is a block. -/
public theorem block_of_blockOK {tab : Nat} {B : Bitset} (h : blockOK tab B = true) : D16 B := by
  rw [blockOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hsub, hcard⟩, hmem⟩, horth⟩, hrec⟩ := h
  have hsub' : ClassSet B := of_decide_eq_true hsub
  have hmem' : ∀ i : Fin 4, byteAt tab i.val ∈ B :=
    fun i => of_decide_eq_true (allFin_true _ hmem i)
  have hlt : ∀ i : Fin 4, byteAt tab i.val < 120 := fun i => lt_of_mem hsub' (hmem' i)
  have horth' : ∀ i j : Fin 4,
      dot (basisOf tab i) (basisOf tab j) = (if i = j then 8 else 0) :=
    fun i j => of_decide_eq_true (allFin_true _ (allFin_true _ horth i) j)
  have hreck : ∀ c : Nat, c < 120 → c ∈ B → Recon (basisOf tab) (repN c) := by
    intro c hc hcB j
    have hb := allLt_true _ _ hrec c hc
    have hm : Bitset.mem B c = true := hcB
    rw [hm] at hb
    have hb2 : reconBool tab c = true := by simpa using hb
    exact of_decide_eq_true (allFin_true _ hb2 j)
  refine ⟨hsub', of_decide_eq_true hcard, basisOf tab, fun i => ?_, indep_of_orth _ horth', ?_⟩
  · refine ⟨D11_repN (hlt i), ?_⟩
    show (D12 (repN (byteAt tab i.val))).val ∈ B
    rw [D12_repN (hlt i)]
    exact hmem' i
  · intro x hx
    obtain ⟨hxR, hxB⟩ := hx
    have hc : (D12 x).val < 120 := (D12 x).isLt
    have hrep : repN (D12 x).val = nrm x := rep_D12 hxR
    have hR := hreck (D12 x).val hc hxB
    refine inSpan_of_recon _ _ ?_
    by_cases hpos : 0 < dot x posRef
    · have : nrm x = x := if_pos hpos
      rw [this] at hrep
      exact hrep ▸ hR
    · have hne : nrm x = AddCommGroup.neg x := if_neg hpos
      rw [hne] at hrep
      have hx2 : AddCommGroup.neg (repN (D12 x).val) = x := by rw [hrep]; exact vneg_neg x
      exact hx2 ▸ hR.neg

/-! ## Union of four class subsets, and the disjointness bookkeeping -/

@[expose] public def union4 (f : Fin 4 → Bitset) : Bitset :=
  Bitset.union (Bitset.union (f 0) (f 1)) (Bitset.union (f 2) (f 3))

public theorem disj_mem {s t : Bitset} (h : Bitset.inter s t = Bitset.empty) {i : Nat}
    (h1 : i ∈ s) (h2 : i ∈ t) : False := by
  have hm : i ∈ Bitset.inter s t := (Bitset.mem_inter s t i).mpr ⟨h1, h2⟩
  rw [h] at hm
  exact Bitset.notMem_empty i hm

public theorem card_union_disj {s t : Bitset} (h : Bitset.inter s t = Bitset.empty) :
    Bitset.card (Bitset.union s t) = Bitset.card s + Bitset.card t := by
  have hc := Bitset.card_union_add_card_inter s t
  rw [h, Bitset.card_empty] at hc
  omega

public theorem classSet_union {s t : Bitset} (hs : ClassSet s) (ht : ClassSet t) :
    ClassSet (Bitset.union s t) := by
  show Bitset.toNat (Bitset.union s t) < 2 ^ 120
  refine Nat.lt_pow_two_of_testBit _ (fun i hi => ?_)
  have hno : ¬ (i ∈ Bitset.union s t) := by
    intro hm
    rcases (Bitset.mem_union s t i).mp hm with h | h
    · exact absurd (lt_of_mem hs h) (by omega)
    · exact absurd (lt_of_mem ht h) (by omega)
  exact Bool.not_eq_true _ |>.mp hno

/-! ## `D17`, `D17a`, `D18`, `D19`, `D22`, `D22a`, `D46a` -/

/-- `D17`. An **AtlasPresentation** is a tuple `(B_0, B_1, B_2, B_3)` of
pairwise-disjoint blocks whose union is tight. It is **ordered**; the ordering
is presentation data and is not redundant, which is why this is a function on
`Fin 4` and not a `Bitset`. -/
public structure D17 where
  blk : Fin 4 → Bitset
  isBlock : ∀ a : Fin 4, D16 (blk a)
  disjoint : ∀ a b : Fin 4, a ≠ b → Bitset.inter (blk a) (blk b) = Bitset.empty
  tight : D15 (union4 blk)

/-- `D17a`. `support(A) := B_0 u B_1 u B_2 u B_3`. -/
@[expose] public def D17a (A : D17) : Bitset := union4 A.blk

/-- `D18`, first half. `V(A) := B_0 u B_1 u B_2 u B_3`. -/
@[expose] public def V (A : D17) : Bitset := union4 A.blk

/-- `D18`, second half. `Rt(A) := { x in R : k(x) in V(A) }`. -/
@[expose] public def Rt (A : D17) (x : Vec 8 Int) : Prop := D11 x ∧ (D12 x).val ∈ V A

/-- `D18`. `V(A)` and `Rt(A)`, bundled so the label names one declaration. -/
@[expose] public def D18 : (D17 → Bitset) × (D17 → Vec 8 Int → Prop) := (V, Rt)

public theorem classSet_V (A : D17) : ClassSet (V A) :=
  classSet_union
    (classSet_union (A.isBlock 0).1 (A.isBlock 1).1)
    (classSet_union (A.isBlock 2).1 (A.isBlock 3).1)

/-- The edge count `sum_{u in S, v in T} [{u,v} in E]`, the numerator of `D19`. -/
@[expose] public def edges (S T : Bitset) : Nat :=
  Vec.sumNat (fun u : K => if u.val ∈ S then D14 T u else 0)

/-- The same count over `Nat` indices, which is the form the kernel runs: the
guard makes the inner degree sum fire only on the `12` classes of `S`. -/
@[expose] public def edgeN (S T : Bitset) : Nat :=
  sumN (fun u => if u ∈ S then degN T u else 0) 120

public theorem edges_eq_edgeN (S T : Bitset) : edges S T = edgeN S T := by
  have h : Vec.sumNat (fun u : K => if u.val ∈ S then D14 T u else 0)
      = Vec.sumNat (fun u : K =>
          (fun c => if c ∈ S then degN T c else 0) u.val) := by
    refine Vec.sumNat_congr (fun u => ?_)
    show (if u.val ∈ S then D14 T u else 0) = if u.val ∈ S then degN T u.val else 0
    by_cases hu : u.val ∈ S
    · rw [if_pos hu, if_pos hu]
      exact D14_eq_degN T u
    · rw [if_neg hu, if_neg hu]
  show Vec.sumNat (fun u : K => if u.val ∈ S then D14 T u else 0) = _
  rw [h]
  exact sumNat_eq_sumN 120 (fun c => if c ∈ S then degN T c else 0)

/-- `D19`. `Q(A)` is the `4 x 4` matrix
`Q[a][b] := ( sum_{u in B_a, v in B_b} [{u,v} in E] ) / |B_a|`, a matrix of
**rational averages**: the division is taken in `Q`, not in `Z`. -/
@[expose] public def D19 (A : D17) (a b : Fin 4) : Rat :=
  ((edges (A.blk a) (A.blk b) : Nat) : Rat) / ((Bitset.card (A.blk a) : Nat) : Rat)

/-- `D22`, first population. `Blk := { B : B is a block }`. -/
@[expose] public def Blk (B : Bitset) : Prop := D16 B

/-- `D22`, second population. `Frm := { {B,B'} : B,B' in Blk, B n B' = empty,
no edge of `E` joins `B` to `B'` }`. -/
@[expose] public def Frm (B B' : Bitset) : Prop :=
  Blk B ∧ Blk B' ∧ Bitset.inter B B' = Bitset.empty
    ∧ ∀ u v : K, u.val ∈ B → v.val ∈ B' → ¬ D13 u v

/-- `D22`, third population. `Atl := { W : W is the union of two disjoint
members of `Frm` and `W` is tight }`. -/
@[expose] public def Atl (W : Bitset) : Prop :=
  ∃ B0 B1 B2 B3 : Bitset,
    Frm B0 B1 ∧ Frm B2 B3
      ∧ Bitset.inter (Bitset.union B0 B1) (Bitset.union B2 B3) = Bitset.empty
      ∧ W = Bitset.union (Bitset.union B0 B1) (Bitset.union B2 B3)
      ∧ D15 W

/-- `D22`. The three populations, bundled so the label names one declaration. -/
@[expose] public def D22 : (Bitset → Prop) × (Bitset → Bitset → Prop) × (Bitset → Prop) :=
  (Blk, Frm, Atl)

/-- `D22a`. An **AtlasInstance** is `W in Atl`, an unordered subset of `K`. -/
@[expose] public def D22a (W : Bitset) : Prop := Atl W

/-- `D46a`. A **BlockFrame** is a member `F = {B,B'}` of `Frm`, an unordered
pair of orthogonal blocks. Unorderedness is `D46a.swap` below: the two
presentations of a `BlockFrame` carry the same `V` and the same `Rt`. -/
public structure D46a where
  fst : Bitset
  snd : Bitset
  isFrm : Frm fst snd

/-- `D46a`. `V(F) := B u B'`. -/
@[expose] public def D46a.V (F : D46a) : Bitset := Bitset.union F.fst F.snd

/-- `D46a`. `Rt(F) := { x in R : k(x) in V(F) }`. -/
@[expose] public def D46a.Rt (F : D46a) (x : Vec 8 Int) : Prop := D11 x ∧ (D12 x).val ∈ F.V

/-- No edge of `E` joins the blocks of a `BlockFrame`, so the relation is
symmetric and `{B,B'}` really is unordered. -/
@[expose] public def D46a.swap (F : D46a) : D46a where
  fst := F.snd
  snd := F.fst
  isFrm := by
    obtain ⟨h1, h2, h3, h4⟩ := F.isFrm
    refine ⟨h2, h1, ?_, fun u v hu hv hd => h4 v u hv hu ⟨fun he => hd.1 he.symm, ?_⟩⟩
    · refine Bitset.ext (fun i => ⟨fun hm => ?_, fun hm => absurd hm (Bitset.notMem_empty i)⟩)
      have h5 := (Bitset.mem_inter F.snd F.fst i).mp hm
      have h6 : i ∈ Bitset.inter F.fst F.snd := (Bitset.mem_inter F.fst F.snd i).mpr ⟨h5.2, h5.1⟩
      rw [h3] at h6
      exact absurd h6 (Bitset.notMem_empty i)
    · rw [dot_comm]; exact hd.2

public theorem D46a.V_swap (F : D46a) : F.swap.V = F.V := by
  refine Bitset.ext (fun i => ?_)
  show i ∈ Bitset.union F.snd F.fst ↔ i ∈ Bitset.union F.fst F.snd
  rw [Bitset.mem_union, Bitset.mem_union]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-! ## The witness AtlasPresentation

`T11` says an AtlasPresentation exists and the document points at a witness in
a file this repository does not have. The witness below is therefore
**constructed here**: four `Bitset` numerals, four orthogonal quadruples
certifying their rank, and two kernel computations -- `blockComp` for `D16`
and `tightComp` for `D15` -- that prove the construction satisfies `D17`
rather than assuming it.

The blocks, as class indices of `UorAtlas.Roots`:

    B_0 = { 0, 1, 2, 3, 4, 5, 14, 15, 16, 17, 26, 27}
    B_1 = { 6, 20, 32, 42, 56, 64, 73, 81, 90, 98, 107, 115}
    B_2 = { 7, 21, 33, 43, 63, 71, 78, 86, 93, 101, 108, 116}
    B_3 = {44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55}

and the orthogonal quadruple certifying each block's rank is
`(0,1,26,27)`, `(6,20,32,42)`, `(7,21,33,43)`, `(44,45,54,55)` respectively. -/

/-- The four orthogonal quadruples, one byte per class index. -/
@[expose] public def blkTab : Fin 4 → Nat := fun a =>
  if a.val = 0 then 454689024
  else if a.val = 1 then 706745350
  else if a.val = 2 then 723588359
  else 926297388

/-- The four blocks, as characteristic numerals. -/
@[expose] public def blkSet : Fin 4 → Bitset := fun a =>
  if a.val = 0 then Bitset.ofNat 201572415
  else if a.val = 1 then Bitset.ofNat 41700952298125245625367265448820800
  else if a.val = 2 then Bitset.ofNat 83403813572612293841978490724810880
  else Bitset.ofNat 72040001851883520

public theorem blockComp : allFin (fun a : Fin 4 => blockOK (blkTab a) (blkSet a)) = true := by
  decide +kernel

public theorem blkIsBlock (a : Fin 4) : D16 (blkSet a) :=
  block_of_blockOK (allFin_true _ blockComp a)

/-- Tightness as one `Bool`, in the form `D60` gives it: `deg_W(v)` against the
constant `24` corrected by `4` on `W`. -/
@[expose] public def tightOK (W : Bitset) : Bool :=
  allLt (fun v => decide (degN W v = (if v ∈ W then 20 else 24))) 120

public theorem tight_of_tightOK {W : Bitset} (h : tightOK W = true) : D15 W := by
  constructor
  · intro v hv
    have hd : degN W v.val = (if v.val ∈ W then 20 else 24) :=
      of_decide_eq_true (allLt_true _ _ h v.val v.isLt)
    rw [D14_eq_degN, hd, if_pos hv]
  · intro v hv
    have hd : degN W v.val = (if v.val ∈ W then 20 else 24) :=
      of_decide_eq_true (allLt_true _ _ h v.val v.isLt)
    rw [D14_eq_degN, hd, if_neg hv]

public theorem tightComp : tightOK (union4 blkSet) = true := by decide +kernel

public theorem blkDisjoint : ∀ a b : Fin 4, a ≠ b →
    Bitset.inter (blkSet a) (blkSet b) = Bitset.empty := by decide +kernel

/-- The witness AtlasPresentation. -/
public def A0 : D17 where
  blk := blkSet
  isBlock := blkIsBlock
  disjoint := blkDisjoint
  tight := tight_of_tightOK tightComp

/-- `T11`. An AtlasPresentation exists. -/
public theorem T11 : Nonempty D17 := ⟨A0⟩

/-! ## `T12` and `T13`: the two counts that hold for **every** AtlasPresentation

Neither needs the census: `|V(A)| = 48` is four disjoint `12`-sets, and
`|Rt(A)| = 96` is `T5`'s root enumeration split at `120`, where the second
half is the antipode of the first and carries the same classes. -/

/-- `T12`. For every AtlasPresentation `A`: `|V(A)| = classes / 2 = 48`. -/
public theorem T12 (A : D17) : Bitset.card (V A) = 48 := by
  have hcross : Bitset.inter (Bitset.union (A.blk 0) (A.blk 1))
      (Bitset.union (A.blk 2) (A.blk 3)) = Bitset.empty := by
    refine Bitset.ext (fun i => ⟨fun hm => ?_, fun hm => absurd hm (Bitset.notMem_empty i)⟩)
    have h1 := (Bitset.mem_inter _ _ i).mp hm
    rcases (Bitset.mem_union _ _ i).mp h1.1 with ha | ha <;>
      rcases (Bitset.mem_union _ _ i).mp h1.2 with hb | hb
    · exact (disj_mem (A.disjoint 0 2 (by decide)) ha hb).elim
    · exact (disj_mem (A.disjoint 0 3 (by decide)) ha hb).elim
    · exact (disj_mem (A.disjoint 1 2 (by decide)) ha hb).elim
    · exact (disj_mem (A.disjoint 1 3 (by decide)) ha hb).elim
  show Bitset.card (Bitset.union (Bitset.union (A.blk 0) (A.blk 1))
    (Bitset.union (A.blk 2) (A.blk 3))) = 48
  rw [card_union_disj hcross, card_union_disj (A.disjoint 0 1 (by decide)),
    card_union_disj (A.disjoint 2 3 (by decide)),
    (A.isBlock 0).2.1, (A.isBlock 1).2.1, (A.isBlock 2).2.1, (A.isBlock 3).2.1]

/-- The indicator of `Rt(A)` along the root enumeration `R240` of `T5`, over
`Nat` indices. -/
@[expose] public def rtIndex (A : D17) (c : Nat) : Nat :=
  ind (V A) (D12 (if c < 120 then repN c else neg (repN (c - 120)))).val

/-- `|Rt(A)|`, counted through the bijection `R240 : Fin 240 -> R` of `T5`. -/
@[expose] public def RtCount (A : D17) : Nat :=
  Vec.sumNat (fun i : Fin 240 => ind (V A) (D12 (R240 i)).val)

/-- `T13`. For every AtlasPresentation `A`:
`|Rt(A)| = classes = scope * stride = 96`. -/
public theorem T13 (A : D17) : RtCount A = 96 := by
  have hN : RtCount A = sumN (rtIndex A) 240 := sumNat_eq_sumN 240 (rtIndex A)
  have h240 : (240 : Nat) = 120 + 120 := by decide
  have hsplit : sumN (rtIndex A) 240
      = sumN (fun k => rtIndex A (k + 120)) 120 + sumN (rtIndex A) 120 := by
    rw [h240]; exact sumN_split (rtIndex A) 120 120
  have hlow : ∀ k, k < 120 → rtIndex A k = ind (V A) k := by
    intro k hk
    show ind (V A) (D12 (if k < 120 then repN k else neg (repN (k - 120)))).val = ind (V A) k
    rw [if_pos hk, D12_repN hk]
  have hhigh : ∀ k, k < 120 → rtIndex A (k + 120) = ind (V A) k := by
    intro k hk
    have hnl : ¬ (k + 120 < 120) := by omega
    have he : k + 120 - 120 = k := by omega
    show ind (V A) (D12 (if k + 120 < 120 then repN (k + 120)
      else neg (repN (k + 120 - 120)))).val = ind (V A) k
    rw [if_neg hnl, he, D12_of_nrm (nrm_neg (D11_repN hk)), D12_repN hk]
  have hcard : sumN (ind (V A)) 120 = 48 := by
    rw [← card_eq_sumN (classSet_V A)]; exact T12 A
  rw [hN, hsplit, sumN_congr_lt _ _ 120 hlow, sumN_congr_lt _ _ 120 hhigh, hcard]

/-! ## `T14`-`T17`, `T16x`, `T61a`: the matrix `Q(A)` of the witness

`Q(A)` is a matrix of rational averages, so the edge counts are computed over
`Nat` once and the division into `Q` is taken afterwards. -/

/-- The edge count `e(B_a, B_b)` of the witness. -/
@[expose] public def edgeTgt (a b : Fin 4) : Nat :=
  if a = b then 96 else if a.val + b.val = 3 then 0 else 72

public theorem edgeComp : allFin (fun a : Fin 4 => allFin (fun b : Fin 4 =>
    decide (edgeN (blkSet a) (blkSet b) = edgeTgt a b))) = true := by decide +kernel

public theorem edges_blkSet (a b : Fin 4) : edges (blkSet a) (blkSet b) = edgeTgt a b := by
  rw [edges_eq_edgeN]
  exact of_decide_eq_true (allFin_true _ (allFin_true _ edgeComp a) b)

public theorem D19_A0 (a b : Fin 4) :
    D19 A0 a b = ((edgeTgt a b : Nat) : Rat) / ((12 : Nat) : Rat) := by
  show ((edges (blkSet a) (blkSet b) : Nat) : Rat) / ((Bitset.card (blkSet a) : Nat) : Rat) = _
  rw [edges_blkSet a b, (blkIsBlock a).2.1]

/-- `T14`. For the witness AtlasPresentation `A`: `Q(A)[a][a] = 8` for all `a`. -/
public theorem T14 : ∀ a : Fin 4, D19 A0 a a = 8 := by
  simp only [D19_A0]
  decide +kernel

/-- `T15`. For the witness AtlasPresentation `A`: `sum_b Q(A)[a][b] = 20` for all `a`. -/
public theorem T15 : ∀ a : Fin 4, Vec.sum (fun b : Fin 4 => D19 A0 a b) = 20 := by
  intro a
  rw [Vec.sum_congr (fun b => D19_A0 a b)]
  revert a
  decide +kernel

/-- `T16`. For the witness AtlasPresentation `A`: the multiset
`{ Q(A)[a][b] : b != a }` is `{0, 6, 6}` for all `a` -- one off-diagonal entry
is `0` and the other two are `6`. -/
public theorem T16 : ∀ a : Fin 4, ∃ p : Fin 4, p ≠ a ∧ D19 A0 a p = 0
    ∧ ∀ b : Fin 4, b ≠ a → b ≠ p → D19 A0 a b = 6 := by
  simp only [D19_A0]
  decide +kernel

/-- The null partner of `T17`: the unique `b != a` with `Q(A)[a][b] = 0`. -/
@[expose] public def nullPartner (a : Fin 4) : Fin 4 :=
  ⟨3 - a.val, Nat.lt_of_le_of_lt (Nat.sub_le 3 a.val) (by decide)⟩

/-- `T17`. For the witness AtlasPresentation `A`: `p(a) :=` the unique `b != a`
with `Q(A)[a][b] = 0` satisfies `p(p(a)) = a` and `p(a) != a`. -/
public theorem T17 :
    (∀ a b : Fin 4, D19 A0 a b = 0 ↔ b = nullPartner a)
      ∧ (∀ a : Fin 4, nullPartner (nullPartner a) = a)
      ∧ (∀ a : Fin 4, nullPartner a ≠ a) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [D19_A0]; decide +kernel
  · decide +kernel
  · decide +kernel

/-- `T61a`. Block `0` has exactly one null partner. -/
public theorem T61a : ∀ b : Fin 4, D19 A0 0 b = 0 ↔ b = nullPartner 0 := T17.1 0

/-- `Q(A)` entry by entry, over `Z`, which is the integrality half of `T16x`. -/
@[expose] public def qInt (a b : Fin 4) : Int :=
  if a = b then 8 else if a.val + b.val = 3 then 0 else 6

public theorem D19_int (a b : Fin 4) : D19 A0 a b = ((qInt a b : Int) : Rat) := by
  simp only [D19_A0]
  revert a b
  decide +kernel

/-- `T16x`. `D19` as rational averages: diagonal `8`, rows summing to `20`, all
integral. -/
public theorem T16x :
    (∀ a : Fin 4, D19 A0 a a = 8)
      ∧ (∀ a : Fin 4, Vec.sum (fun b : Fin 4 => D19 A0 a b) = 20)
      ∧ (∀ a b : Fin 4, ∃ n : Int, D19 A0 a b = ((n : Int) : Rat)) :=
  ⟨T14, T15, fun a b => ⟨qInt a b, D19_int a b⟩⟩

/-- `T10b`. `A.chi = -4.chi + 24.1` for the witness. -/
public theorem T10b : ∀ v : K,
    (D14 (V A0) v : Int) = -4 * (if v.val ∈ V A0 then 1 else 0) + 24 :=
  (T10c (V A0)).mpr A0.tight

/-! ## The witness support is a BlockFrame pair and an AtlasInstance

`D22`'s `Frm` and `Atl` and `D46a`'s BlockFrame are inhabited here rather than
merely defined: `{B_0,B_3}` and `{B_1,B_2}` are the two BlockFrames of the
witness, exactly the null pairs `T17` names, and their union is `V(A_0)`. -/

@[expose] public def noEdgeOK (B B' : Bitset) : Bool :=
  allLt (fun u => !(Bitset.mem B u)
    || allLt (fun v => !(Bitset.mem B' v) || decide (adjN u v = 0)) 120) 120

public theorem noEdge_of {B B' : Bitset} (h : noEdgeOK B B' = true) :
    ∀ u v : K, u.val ∈ B → v.val ∈ B' → ¬ D13 u v := by
  intro u v hu hv hd
  have hmu : Bitset.mem B u.val = true := hu
  have hmv : Bitset.mem B' v.val = true := hv
  have h1 := allLt_true _ _ h u.val u.isLt
  rw [hmu] at h1
  have h2 : allLt (fun v => !(Bitset.mem B' v) || decide (adjN u.val v = 0)) 120 = true := by
    simpa using h1
  have h3 := allLt_true _ _ h2 v.val v.isLt
  rw [hmv] at h3
  have h4 : adjN u.val v.val = 0 := of_decide_eq_true (by simpa using h3)
  have h5 : A u v = 1 := A_of_D13 hd
  rw [show A u v = adjN u.val v.val from rfl, h4] at h5
  exact Nat.noConfusion h5

public theorem frm03 : Frm (blkSet 0) (blkSet 3) :=
  ⟨blkIsBlock 0, blkIsBlock 3, blkDisjoint 0 3 (by decide), noEdge_of (by decide +kernel)⟩

public theorem frm12 : Frm (blkSet 1) (blkSet 2) :=
  ⟨blkIsBlock 1, blkIsBlock 2, blkDisjoint 1 2 (by decide), noEdge_of (by decide +kernel)⟩

/-- `D46a`. The first BlockFrame of the witness. -/
@[expose] public def frame0 : D46a := ⟨blkSet 0, blkSet 3, frm03⟩

/-- `D46a`. The second BlockFrame of the witness. -/
@[expose] public def frame1 : D46a := ⟨blkSet 1, blkSet 2, frm12⟩

/-- The witness support is an AtlasInstance: it is the union of the two
disjoint BlockFrames `frame0`, `frame1` and it is tight. -/
public theorem atl_A0 : Atl (V A0) := by
  refine ⟨blkSet 0, blkSet 3, blkSet 1, blkSet 2, frm03, frm12, ?_, ?_, A0.tight⟩
  · decide +kernel
  · decide +kernel

/-- `D22a`. The witness support is an AtlasInstance. -/
public theorem D22a_A0 : D22a (V A0) := atl_A0

/-! ## `T19` -/

/-- `T19`. For the witness AtlasPresentation `A`: there exist `x, y in Rt(A)`
with `<x,y> = -1` and `x + y in R \ Rt(A)`. In the 2x scaling `<x,y> = -1`
reads as `dot x y = -4`; the witnesses are the representatives of classes `1`
and `20`, whose sum is the representative of class `8`, which is a root and is
not in `V(A)`. -/
public theorem T19 : ∃ x y : Vec 8 Int, Rt A0 x ∧ Rt A0 y ∧ dot x y = -4
    ∧ D11 (AddCommGroup.add x y) ∧ ¬ Rt A0 (AddCommGroup.add x y) := by
  refine ⟨repN 1, repN 20, ⟨D11_repN (by decide), ?_⟩, ⟨D11_repN (by decide), ?_⟩, ?_, ?_, ?_⟩
  · rw [D12_repN (by decide)]; decide +kernel
  · rw [D12_repN (by decide)]; decide +kernel
  · decide +kernel
  · exact (isD11_iff _).mp (by decide +kernel)
  · exact fun h => absurd h.2 (by decide +kernel)
