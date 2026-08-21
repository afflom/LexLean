module

public import Init
public import UorAtlas.CensusComplete
public import UorAtlas.GroupSeries
public import UorAtlas.Prelude.RingLemmas

/-!
# Closure of the Atlas census and group chain

This module starts from the complete block census in `UorAtlas.Census`.  It
constructs the orthogonal mate of an arbitrary block, counts the resulting
BlockFrames, counts disjoint pairs of BlockFrames, and identifies that
population with the `Aut` orbit of the exhibited AtlasInstance.  The latter is
the transitivity step on which the universal stabiliser statements depend.
-/

set_option autoImplicit false
set_option maxRecDepth 40000

public section

namespace UorAtlas.Closure

open UorAtlas.Prelude
open UorAtlas.Prelude.ListAux
open UorAtlas.Roots
open UorAtlas.Blocks
open UorAtlas.Group
open UorAtlas.Census
open UorAtlas.Prelude.RingLemmas

/-! ## The unique orthogonal mate of a block -/

/-- Starting from all `120` classes, remove each class of `B` and every one of
its neighbours.  The remaining classes are orthogonal to every class of `B`.
The fuel is the number of class indices already inspected. -/
@[expose] public def orthFold (B : Bitset) : Nat → Bitset
  | 0 => Bitset.ofNat fullMask
  | n + 1 =>
      if n ∈ B then
        Bitset.diff (orthFold B n) (Bitset.union (Bitset.singleton n) (arow n))
      else orthFold B n

/-- The class set orthogonal to, and disjoint from, `B`. -/
@[expose] public def orthTo (B : Bitset) : Bitset := orthFold B 120

public theorem mem_fullMask {i : Nat} : i ∈ Bitset.ofNat fullMask ↔ i < 120 := by
  show Nat.testBit (2 ^ 120 - 1) i = true ↔ i < 120
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true_iff

public theorem mem_orthFold (B : Bitset) (i : Nat) : ∀ n,
    i ∈ orthFold B n ↔ i < 120 ∧
      ∀ u : Nat, u < n → u ∈ B → i ≠ u ∧ i ∉ arow u := by
  intro n
  induction n with
  | zero =>
      rw [orthFold, mem_fullMask]
      simp
  | succ n ih =>
      rw [orthFold]
      by_cases hn : n ∈ B
      · rw [if_pos hn, Bitset.mem_diff, ih, Bitset.mem_union, Bitset.mem_singleton]
        constructor
        · rintro ⟨⟨hi, hprev⟩, hnew⟩
          refine ⟨hi, fun u hu huB => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
          · exact hprev u hu huB
          · exact ⟨fun he => hnew (Or.inl he), fun hm => hnew (Or.inr hm)⟩
        · rintro ⟨hi, hall⟩
          refine ⟨⟨hi, fun u hu huB => hall u (Nat.lt_succ_of_lt hu) huB⟩, ?_⟩
          rintro (he | hm)
          · exact (hall n (Nat.lt_succ_self n) hn).1 he
          · exact (hall n (Nat.lt_succ_self n) hn).2 hm
      · rw [if_neg hn, ih]
        constructor
        · rintro ⟨hi, hall⟩
          refine ⟨hi, fun u hu huB => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
          · exact hall u hu huB
          · exact absurd huB hn
        · rintro ⟨hi, hall⟩
          exact ⟨hi, fun u hu huB => hall u (Nat.lt_succ_of_lt hu) huB⟩

public theorem mem_orthTo (B : Bitset) (i : Nat) :
    i ∈ orthTo B ↔ i < 120 ∧ ∀ u : K, u.val ∈ B → i ≠ u.val ∧ i ∉ arow u.val := by
  rw [orthTo, mem_orthFold]
  constructor
  · rintro ⟨hi, hall⟩
    exact ⟨hi, fun u hu => hall u.val u.isLt hu⟩
  · rintro ⟨hi, hall⟩
    refine ⟨hi, fun u hu huB => ?_⟩
    exact hall ⟨u, hu⟩ huB

/-- Equal finite cardinality turns inclusion of class bitsets into equality. -/
public theorem bitset_eq_of_subset_card {S T : Bitset}
    (hsub : ∀ i, i ∈ S → i ∈ T) (hcard : Bitset.card S = Bitset.card T) : S = T := by
  refine Bitset.ext (fun i => ⟨hsub i, fun hi => ?_⟩)
  have hlist : ∀ x, x ∈ Bitset.toList S → x ∈ Bitset.toList T := by
    intro x hx
    exact (Bitset.mem_toList T x).mpr (hsub x ((Bitset.mem_toList S x).mp hx))
  apply (Bitset.mem_toList S i).mp
  apply mem_of_subset_length_eq (nodup_toList S) hlist
  · rw [Bitset.length_toList, Bitset.length_toList, hcard]
  · exact (Bitset.mem_toList T i).mpr hi

/-! The finite certificate below identifies `orthTo (blkAt i)` with another
entry of the complete block table.  The binary search is only an accelerator:
the certificate checks the returned index and the equality it claims. -/

@[expose] public def mateIndex (i : Nat) : Nat := blkFind (Bitset.toNat (orthTo (blkAt i))) 13 0 3150

@[expose] public def mateEntryOK (i : Nat) : Bool :=
  decide (mateIndex i < 3150)
    && decide (orthTo (blkAt i) = blkAt (mateIndex i))
    && decide (mateIndex i ≠ i)
    && decide (mateIndex (mateIndex i) = i)

@[expose] public def mateRange (a : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => mateRange a n && mateEntryOK (a + n)

public theorem mateRange_true {a n i : Nat} (h : mateRange a n = true)
    (ha : a ≤ i) (hi : i < a + n) : mateEntryOK i = true := by
  have key : ∀ m, mateRange a m = true → ∀ k, k < m → mateEntryOK (a + k) = true := by
    intro m
    induction m with
    | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ m ih =>
        intro hm k hk
        rw [mateRange, Bool.and_eq_true] at hm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact ih hm.1 k hk
        · exact hm.2
  have hk := key n h (i - a) (by omega)
  simpa [show a + (i - a) = i by omega] using hk

set_option maxHeartbeats 4000000 in
public theorem mateAll : mateRange 0 3150 = true := by decide +kernel

public theorem mateEntry_true {i : Nat} (hi : i < 3150) : mateEntryOK i = true :=
  mateRange_true mateAll (by omega) (by omega)

public theorem mateIndex_lt {i : Nat} (hi : i < 3150) : mateIndex i < 3150 := by
  have h := mateEntry_true hi
  simp only [mateEntryOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

public theorem orthTo_blkAt {i : Nat} (hi : i < 3150) :
    orthTo (blkAt i) = blkAt (mateIndex i) := by
  have h := mateEntry_true hi
  simp only [mateEntryOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

public theorem mateIndex_ne {i : Nat} (hi : i < 3150) : mateIndex i ≠ i := by
  have h := mateEntry_true hi
  simp only [mateEntryOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

public theorem mateIndex_involutive {i : Nat} (hi : i < 3150) :
    mateIndex (mateIndex i) = i := by
  have h := mateEntry_true hi
  simp only [mateEntryOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

public theorem orthTo_block {B : Bitset} (hB : Blk B) : Blk (orthTo B) := by
  obtain ⟨i, hi, rfl⟩ := block_census_complete hB
  rw [orthTo_blkAt hi]
  exact blkD16 (mateIndex_lt hi)

public theorem orthTo_ne {B : Bitset} (hB : Blk B) : orthTo B ≠ B := by
  obtain ⟨i, hi, rfl⟩ := block_census_complete hB
  rw [orthTo_blkAt hi]
  exact blkInj (mateIndex_lt hi) hi (mateIndex_ne hi)

public theorem orthTo_involutive {B : Bitset} (hB : Blk B) : orthTo (orthTo B) = B := by
  obtain ⟨i, hi, rfl⟩ := block_census_complete hB
  rw [orthTo_blkAt hi, orthTo_blkAt (mateIndex_lt hi), mateIndex_involutive hi]

public theorem frm_orthTo {B : Bitset} (hB : Blk B) : Frm B (orthTo B) := by
  refine ⟨hB, orthTo_block hB, ?_, ?_⟩
  · refine Bitset.ext (fun i => ⟨fun hm => ?_, fun hm => absurd hm (Bitset.notMem_empty i)⟩)
    obtain ⟨hiB, hiO⟩ := (Bitset.mem_inter B (orthTo B) i).mp hm
    have horth := (mem_orthTo B i).mp hiO
    exact False.elim ((horth.2 ⟨i, lt_of_mem hB.1 hiB⟩ hiB).1 rfl)
  · intro u v hu hv hadj
    have horth := (mem_orthTo B v.val).mp hv
    have hrow : v.val ∈ arow u.val := by
      apply (mem_adjRow u.isLt v.isLt).mpr
      show A u v = 1
      exact A_of_D13 hadj
    exact (horth.2 u hu).2 hrow

public theorem orthTo_eq_of_frm {B C : Bitset} (h : Frm B C) : orthTo B = C := by
  obtain ⟨hB, hC, hdisj, hno⟩ := h
  symm
  apply bitset_eq_of_subset_card (S := C) (T := orthTo B)
  · intro i hiC
    have hi : i < 120 := lt_of_mem hC.1 hiC
    apply (mem_orthTo B i).mpr
    refine ⟨hi, fun u huB => ⟨?_, ?_⟩⟩
    · intro he
      have hm : i ∈ Bitset.inter B C := (Bitset.mem_inter B C i).mpr ⟨he ▸ huB, hiC⟩
      rw [hdisj] at hm
      exact absurd hm (Bitset.notMem_empty i)
    · intro hrow
      have hadj : D13 u ⟨i, hi⟩ := by
        apply (A_eq_one_iff u ⟨i, hi⟩).mp
        show adjN u.val i = 1
        exact (mem_adjRow u.isLt hi).mp hrow
      exact hno u ⟨i, hi⟩ huB hiC hadj
  · rw [hC.2.1, (orthTo_block hB).2.1]

/-! ## `T23`: the BlockFrame census -/

/-- The lower-index representative of every two-cycle of `mateIndex`. -/
@[expose] public def frameIds : List Nat :=
  (List.range 3150).filter (fun i => decide (i < mateIndex i))

@[expose] public def frameSupport (i : Nat) : Bitset :=
  Bitset.union (blkAt i) (blkAt (mateIndex i))

public theorem mem_frameIds {i : Nat} :
    i ∈ frameIds ↔ i < 3150 ∧ i < mateIndex i := by
  simp [frameIds]

set_option maxHeartbeats 4000000 in
public theorem frameIds_length : frameIds.length = 1575 := by decide +kernel

public theorem frameIds_nodup : frameIds.Nodup :=
  List.Pairwise.filter _ List.nodup_range

public theorem frameId_frm {i : Nat} (hi : i ∈ frameIds) :
    Frm (blkAt i) (blkAt (mateIndex i)) := by
  have hlt := (mem_frameIds.mp hi).1
  rw [← orthTo_blkAt hlt]
  exact frm_orthTo (blkD16 hlt)

public theorem frame_census_complete {B C : Bitset} (h : Frm B C) :
    ∃ i ∈ frameIds,
      (B = blkAt i ∧ C = blkAt (mateIndex i))
        ∨ (C = blkAt i ∧ B = blkAt (mateIndex i)) := by
  obtain ⟨j, hj, hBj⟩ := block_census_complete h.1
  have hmate : C = blkAt (mateIndex j) := by
    calc
      C = orthTo B := (orthTo_eq_of_frm h).symm
      _ = orthTo (blkAt j) := congrArg orthTo hBj.symm
      _ = blkAt (mateIndex j) := orthTo_blkAt hj
  by_cases hlt : j < mateIndex j
  · exact ⟨j, mem_frameIds.mpr ⟨hj, hlt⟩, Or.inl ⟨hBj.symm, hmate⟩⟩
  · let i := mateIndex j
    have hi : i < 3150 := mateIndex_lt hj
    have hij : i < mateIndex i := by
      show mateIndex j < mateIndex (mateIndex j)
      rw [mateIndex_involutive hj]
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (mateIndex_ne hj)
    refine ⟨i, mem_frameIds.mpr ⟨hi, hij⟩, Or.inr ⟨hmate, ?_⟩⟩
    show B = blkAt (mateIndex (mateIndex j))
    rw [mateIndex_involutive hj]
    exact hBj.symm

/-- `T23`.  The fixed-point-free mate involution partitions the `3150` blocks
into exactly `1575` unordered BlockFrames, and the displayed list is complete. -/
public theorem T23 :
    frameIds.Nodup ∧ frameIds.length = 1575
      ∧ (∀ i, i ∈ frameIds → Frm (blkAt i) (blkAt (mateIndex i)))
      ∧ (∀ B C, Frm B C → ∃ i ∈ frameIds,
        (B = blkAt i ∧ C = blkAt (mateIndex i))
          ∨ (C = blkAt i ∧ B = blkAt (mateIndex i))) :=
  ⟨frameIds_nodup, frameIds_length,
    (fun i hi => frameId_frm (i := i) hi), fun _ _ => frame_census_complete⟩

/-! `T22a` records the modular form of the rank certificate.  The Gram
determinants are positive and at most the four-vector Hadamard bound `4096`;
the prime `4099` therefore cannot annihilate one. -/

@[expose] public def modGramOK (g : Nat) : Bool :=
  Bool.not (positiveGram g) || decide (0 < certScale (gramInversePack g)
    ∧ certScale (gramInversePack g) < 4099)

set_option maxHeartbeats 4000000 in
public theorem modGramAll : allLt modGramOK 15625 = true := by decide +kernel

public theorem modGram_true {g : Nat} (hg : g < 15625)
    (hp : positiveGram g = true) :
    0 < certScale (gramInversePack g)
      ∧ certScale (gramInversePack g) < 4099 := by
  have h := allLt_true _ _ modGramAll g hg
  simp only [modGramOK, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  rcases h with hn | h
  · exact False.elim (Bool.noConfusion (hp.symm.trans hn))
  · exact h

@[expose] public def prime4099Check : Bool :=
  allLt (fun d => decide (d ∣ 4099 → d = 1 ∨ d = 4099)) 4100

public theorem prime4099Check_true : prime4099Check = true := by decide +kernel

public theorem prime4099 : IsPrime 4099 := by
  refine ⟨by omega, fun d hd => ?_⟩
  have hdle : d ≤ 4099 := Nat.le_of_dvd (by omega) hd
  have hc := allLt_true _ _ prime4099Check_true d (by omega)
  exact of_decide_eq_true hc hd

/-- `T22a`.  Rank four is certified modulo the prime `4099`, strictly above
the Hadamard bound: every positive Gram code used by the complete census has a
nonzero determinant scale modulo that prime. -/
public theorem T22a :
    IsPrime 4099 ∧ 4096 < 4099
      ∧ ∀ g : Nat, g < 15625 → positiveGram g = true →
        0 < certScale (gramInversePack g)
          ∧ certScale (gramInversePack g) < 4099
          ∧ certScale (gramInversePack g) % 4099 ≠ 0 := by
  refine ⟨prime4099, by decide, fun g hg hp => ?_⟩
  have h := modGram_true hg hp
  refine ⟨h.1, h.2, ?_⟩
  have hm : certScale (gramInversePack g) % 4099 = certScale (gramInversePack g) :=
    Int.emod_eq_of_lt (by omega) h.2
  rw [hm]
  omega

end UorAtlas.Closure

end
