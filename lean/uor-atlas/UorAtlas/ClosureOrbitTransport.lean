module

public import Init
public import UorAtlas.ClosureOrbitCount

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

/-! ## The frame-pair population is the orbit -/

public theorem frameSupport_eq {B C : Bitset} (h : Frm B C) :
    ∃ i ∈ frameIds, Bitset.union B C = frameSupport i := by
  obtain ⟨i, hi, hcase⟩ := frame_census_complete h
  refine ⟨i, hi, ?_⟩
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · refine Bitset.ext (fun k => ?_)
    simp only [frameSupport, Bitset.mem_union]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

public theorem frameSupport_card {i : Nat} (hi : i ∈ frameIds) :
    Bitset.card (frameSupport i) = 24 := by
  have hf := frameId_frm hi
  show Bitset.card (Bitset.union (blkAt i) (blkAt (mateIndex i))) = 24
  rw [card_union_disj hf.2.2.1, hf.1.2.1, hf.2.1.2.1]

public theorem two_frames_candidate {B0 B1 B2 B3 : Bitset}
    (hF : Frm B0 B1) (hG : Frm B2 B3)
    (hd : Bitset.inter (Bitset.union B0 B1) (Bitset.union B2 B3) = Bitset.empty) :
    Bitset.union (Bitset.union B0 B1) (Bitset.union B2 B3) ∈ atlasSupports := by
  obtain ⟨i, hi, hFi⟩ := frameSupport_eq hF
  obtain ⟨j, hj, hGj⟩ := frameSupport_eq hG
  have hij : i ≠ j := by
    intro he
    subst j
    have hsame : Bitset.union B0 B1 = Bitset.union B2 B3 := hFi.trans hGj.symm
    have hempty : Bitset.inter (Bitset.union B0 B1) (Bitset.union B0 B1) =
        Bitset.empty := by
      calc
        Bitset.inter (Bitset.union B0 B1) (Bitset.union B0 B1) =
            Bitset.inter (Bitset.union B0 B1) (Bitset.union B2 B3) :=
          congrArg (Bitset.inter (Bitset.union B0 B1)) hsame
        _ = Bitset.empty := hd
    have hzero : Bitset.card (Bitset.union B0 B1) = 0 := by
      have hself : Bitset.inter (Bitset.union B0 B1) (Bitset.union B0 B1) =
          Bitset.union B0 B1 := by
        refine Bitset.ext (fun k => ?_)
        rw [Bitset.mem_inter]
        exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
      have hz : Bitset.union B0 B1 = Bitset.empty := hself.symm.trans hempty
      rw [hz]
      decide
    have hcard := frameSupport_card hi
    rw [← hFi] at hcard
    rw [hcard] at hzero
    omega
  rcases Nat.lt_or_gt_of_ne hij with hij | hji
  · apply mem_atlasSupports.mpr
    exact ⟨i, j, ⟨hi, hj, hij, by rwa [← hFi, ← hGj]⟩,
      by rw [pairSupport, hFi, hGj]⟩
  · apply mem_atlasSupports.mpr
    refine ⟨j, i, ⟨hj, hi, hji, ?_⟩, ?_⟩
    · rw [← hGj, ← hFi]
      refine Bitset.ext (fun k => ?_)
      rw [Bitset.mem_inter]
      constructor
      · intro h
        have hm : k ∈ Bitset.inter (Bitset.union B0 B1) (Bitset.union B2 B3) :=
          (Bitset.mem_inter _ _ k).mpr ⟨h.2, h.1⟩
        rw [hd] at hm
        exact False.elim (absurd hm (Bitset.notMem_empty k))
      · intro h
        exact False.elim (absurd h (Bitset.notMem_empty k))
    · refine Bitset.ext (fun k => ?_)
      rw [pairSupport, ← hGj, ← hFi]
      constructor
      · intro h
        exact (Bitset.mem_union _ _ k).mpr ((Bitset.mem_union _ _ k).mp h).symm
      · intro h
        exact (Bitset.mem_union _ _ k).mpr ((Bitset.mem_union _ _ k).mp h).symm

public theorem atl_mem_atlasSupports {W : Bitset} (hW : Atl W) : W ∈ atlasSupports := by
  obtain ⟨B0, B1, B2, B3, hF, hG, hd, rfl, _⟩ := hW
  exact two_frames_candidate hF hG hd

public theorem W0_two_frames :
    Bitset.union Blocks.frame0.V Blocks.frame1.V = W0 := by
  refine Bitset.ext (fun k => ?_)
  simp only [Blocks.D46a.V, Blocks.frame0, Blocks.frame1, W0, Blocks.union4,
    Bitset.mem_union]
  constructor
  · intro h
    rcases h with h03 | h12
    · rcases h03 with h0 | h3
      · exact Or.inl (Or.inl h0)
      · exact Or.inr (Or.inr h3)
    · rcases h12 with h1 | h2
      · exact Or.inl (Or.inr h1)
      · exact Or.inr (Or.inl h2)
  · intro h
    rcases h with h01 | h23
    · rcases h01 with h0 | h1
      · exact Or.inl (Or.inl h0)
      · exact Or.inr (Or.inl h1)
    · rcases h23 with h2 | h3
      · exact Or.inr (Or.inr h2)
      · exact Or.inl (Or.inr h3)

public theorem orbit_mem_atlasSupports {g : Perm 120} (hg : D21 g) :
    actP g W0 ∈ atlasSupports := by
  have hF := aut_frm hg Blocks.frm03
  have hG := aut_frm hg Blocks.frm12
  have hd0 : Bitset.inter Blocks.frame0.V Blocks.frame1.V = Bitset.empty := by
    refine Bitset.ext (fun i => ⟨fun hi => ?_, fun hi => absurd hi (Bitset.notMem_empty i)⟩)
    obtain ⟨hi03, hi12⟩ := (Bitset.mem_inter _ _ i).mp hi
    rcases (Bitset.mem_union _ _ i).mp hi03 with hi0 | hi3
    · rcases (Bitset.mem_union _ _ i).mp hi12 with hi1 | hi2
      · exact False.elim (disj_mem (Blocks.blkDisjoint 0 1 (by decide)) hi0 hi1)
      · exact False.elim (disj_mem (Blocks.blkDisjoint 0 2 (by decide)) hi0 hi2)
    · rcases (Bitset.mem_union _ _ i).mp hi12 with hi1 | hi2
      · exact False.elim (disj_mem (Blocks.blkDisjoint 3 1 (by decide)) hi3 hi1)
      · exact False.elim (disj_mem (Blocks.blkDisjoint 3 2 (by decide)) hi3 hi2)
  have hd : Bitset.inter
      (Bitset.union (actP g Blocks.frame0.fst) (actP g Blocks.frame0.snd))
      (Bitset.union (actP g Blocks.frame1.fst) (actP g Blocks.frame1.snd)) = Bitset.empty := by
    have hd0' : Bitset.inter
        (Bitset.union Blocks.frame0.fst Blocks.frame0.snd)
        (Bitset.union Blocks.frame1.fst Blocks.frame1.snd) = Bitset.empty := by
      simpa only [Blocks.D46a.V] using hd0
    rw [← actP_union, ← actP_union, ← actP_inter, hd0', actP_empty]
  have hm := two_frames_candidate hF hG hd
  have hW0' : Bitset.union
      (Bitset.union Blocks.frame0.fst Blocks.frame0.snd)
      (Bitset.union Blocks.frame1.fst Blocks.frame1.snd) = W0 := by
    simpa only [Blocks.D46a.V] using W0_two_frames
  have hW0'' : Bitset.union
      (Bitset.union (Blocks.blkSet 0) (Blocks.blkSet 3))
      (Bitset.union (Blocks.blkSet 1) (Blocks.blkSet 2)) = W0 := by
    simpa only [Blocks.frame0, Blocks.frame1] using hW0'
  rw [← actP_union, ← actP_union, ← actP_union, hW0''] at hm
  exact hm

public theorem orbit_equals_candidates : ∃ O : List Bitset,
    O.Nodup ∧ O.length = 75600
      ∧ (∀ W, W ∈ O ↔ W ∈ atlasSupports)
      ∧ (∀ W, W ∈ O ↔ ∃ g : Perm 120, D21 g ∧ actP g W0 = W) := by
  obtain ⟨O, hOnd, hOlen, hO⟩ := orbit_count
  have hsub : ∀ W, W ∈ O → W ∈ atlasSupports := by
    intro W hW
    obtain ⟨g, hg, rfl⟩ := (hO W).mp hW
    exact orbit_mem_atlasSupports hg
  have hback : ∀ W, W ∈ atlasSupports → W ∈ O := by
    intro W hW
    apply mem_of_subset_length_eq hOnd hsub
    · rw [hOlen, atlasSupports_length]
    · exact hW
  exact ⟨O, hOnd, hOlen, fun W => ⟨hsub W, hback W⟩, hO⟩

public theorem candidate_tight {W : Bitset} (hW : W ∈ atlasSupports) : D15 W := by
  obtain ⟨O, _, _, hOC, hO⟩ := orbit_equals_candidates
  obtain ⟨g, hg, rfl⟩ := (hO W).mp ((hOC W).mpr hW)
  rw [← W0_eq]
  exact aut_tight hg Blocks.A0.tight

public theorem candidate_atl {W : Bitset} (hW : W ∈ atlasSupports) : Atl W := by
  obtain ⟨i, j, hp, rfl⟩ := mem_atlasSupports.mp hW
  refine ⟨blkAt i, blkAt (mateIndex i), blkAt j, blkAt (mateIndex j),
    frameId_frm hp.1, frameId_frm hp.2.1, hp.2.2.2, rfl, ?_⟩
  exact candidate_tight hW

/-- `T27`.  `Atl` is exactly the single `Aut` orbit of the witness
AtlasInstance. -/
public theorem T27 (W : Bitset) :
    Atl W ↔ ∃ g : Perm 120, D21 g ∧ actP g W0 = W := by
  obtain ⟨O, _, _, hOC, hO⟩ := orbit_equals_candidates
  constructor
  · intro hW
    exact (hO W).mp ((hOC W).mpr (atl_mem_atlasSupports hW))
  · intro hW
    exact candidate_atl ((hOC W).mp ((hO W).mpr hW))

/-- `T24`.  The `75600`-element orbit list is a duplicate-free and exhaustive
enumeration of `Atl`; every disjoint pair of BlockFrames is tight because it
lies in that orbit. -/
public theorem T24 : ∃ L : List Bitset,
    L.Nodup ∧ L.length = 75600 ∧ (∀ W : Bitset, W ∈ L ↔ Atl W) := by
  obtain ⟨O, hOnd, hOlen, _, hO⟩ := orbit_equals_candidates
  exact ⟨O, hOnd, hOlen, fun W => (hO W).trans (T27 W).symm⟩

/-! ## `T25` and `T25x`: the four blocks in an instance -/

@[expose] public def ContainedBlock (W B : Bitset) : Prop :=
  Blk B ∧ ∀ i, i ∈ B → i ∈ W

@[expose] public def blockIncluded (W : Bitset) (i : Nat) : Bool :=
  decide (Bitset.diff (blkAt i) W = Bitset.empty)

public theorem blockIncluded_true_iff {W : Bitset} {i : Nat} :
    blockIncluded W i = true ↔ ∀ k, k ∈ blkAt i → k ∈ W := by
  simp only [blockIncluded, decide_eq_true_eq]
  constructor
  · intro he k hk
    by_cases hkW : k ∈ W
    · exact hkW
    · have hm : k ∈ Bitset.diff (blkAt i) W :=
        (Bitset.mem_diff _ _ k).mpr ⟨hk, hkW⟩
      rw [he] at hm
      exact False.elim (absurd hm (Bitset.notMem_empty k))
  · intro hsub
    refine Bitset.ext (fun k => ?_)
    rw [Bitset.mem_diff]
    constructor
    · rintro ⟨hk, hn⟩
      exact False.elim (hn (hsub k hk))
    · intro hm
      exact False.elim (absurd hm (Bitset.notMem_empty k))

@[expose] public def blockIdsIn (W : Bitset) : List Nat :=
  (List.range 3150).filter (blockIncluded W)

@[expose] public def blockSetsIn (W : Bitset) : List Bitset :=
  (blockIdsIn W).map blkAt

public theorem mem_blockIdsIn {W : Bitset} {i : Nat} :
    i ∈ blockIdsIn W ↔ i < 3150 ∧ ∀ k, k ∈ blkAt i → k ∈ W := by
  simp only [blockIdsIn, List.mem_filter, List.mem_range]
  rw [blockIncluded_true_iff]

public theorem blockIdsIn_nodup (W : Bitset) : (blockIdsIn W).Nodup :=
  List.Pairwise.filter _ List.nodup_range

public theorem blockSetsIn_nodup (W : Bitset) : (blockSetsIn W).Nodup := by
  apply nodup_map_on blkAt (blockIdsIn W) (blockIdsIn_nodup W)
  intro i hi j hj he
  have hi' := (mem_blockIdsIn.mp hi).1
  have hj' := (mem_blockIdsIn.mp hj).1
  by_cases hij : i = j
  · exact hij
  · exact False.elim ((blkInj hi' hj' hij) he)

public theorem mem_blockSetsIn {W B : Bitset} :
    B ∈ blockSetsIn W ↔ ContainedBlock W B := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have hd := mem_blockIdsIn.mp hi
    exact ⟨blkD16 hd.1, hd.2⟩
  · rintro ⟨hB, hsub⟩
    obtain ⟨i, hi, rfl⟩ := block_census_complete hB
    exact List.mem_map.mpr ⟨i, mem_blockIdsIn.mpr ⟨hi, hsub⟩, rfl⟩

set_option maxHeartbeats 4000000 in
public theorem witness_block_count : (blockSetsIn W0).length = 4 := by decide +kernel

/-- `W` contains exactly `n` blocks. -/
@[expose] public def HasBlockCount (W : Bitset) (n : Nat) : Prop :=
  ∃ L : List Bitset, L.Nodup ∧ L.length = n ∧ ∀ B, B ∈ L ↔ ContainedBlock W B

/-- `T25`.  The witness AtlasInstance contains exactly its four displayed
blocks. -/
public theorem T25 : HasBlockCount W0 4 :=
  ⟨blockSetsIn W0, blockSetsIn_nodup W0, witness_block_count, fun _ => mem_blockSetsIn⟩

public theorem actP_subset (g : Perm 120) {S T : Bitset}
    (h : ∀ i, i ∈ S → i ∈ T) :
    ∀ i, i ∈ actP g S → i ∈ actP g T := by
  intro i hi
  obtain ⟨u, hu, he⟩ := (mem_actP g S i).mp hi
  exact (mem_actP g T i).mpr ⟨u, h u.val hu, he⟩

public theorem HasBlockCount.image {g : Perm 120} (hg : D21 g)
    {W : Bitset} (hW : ClassSet W) {n : Nat} (h : HasBlockCount W n) :
    HasBlockCount (actP g W) n := by
  obtain ⟨L, hnd, hlen, hmem⟩ := h
  let M := L.map (actP g)
  refine ⟨M, ?_, by simp [M, hlen], fun B => ?_⟩
  · apply nodup_map_on (actP g) L hnd
    intro B hB C hC he
    have hBC : ClassSet B := (hmem B).mp hB |>.1.1
    have hCC : ClassSet C := (hmem C).mp hC |>.1.1
    exact actP_inj g hBC hCC he
  · constructor
    · intro hBM
      obtain ⟨C, hCL, rfl⟩ := List.mem_map.mp hBM
      have hC := (hmem C).mp hCL
      exact ⟨aut_block hg hC.1, actP_subset g hC.2⟩
    · rintro ⟨hBB, hsub⟩
      let C := actP g.inv B
      have hgInv : D21 g.inv := Perm.Gen.inv_mem hg
      have hCB : Blk C := aut_block hgInv hBB
      have hCW : ∀ i, i ∈ C → i ∈ W := by
        have hs := actP_subset g.inv hsub
        intro i hi
        have : i ∈ actP g.inv (actP g W) := hs i hi
        rwa [actP_inv g hW] at this
      have hCL : C ∈ L := (hmem C).mpr ⟨hCB, hCW⟩
      refine List.mem_map.mpr ⟨C, hCL, ?_⟩
      show actP g (actP g.inv B) = B
      rw [← actP_comp, Perm.comp_inv, actP_one hBB.1]

/-- `T25x`.  Every AtlasInstance contains exactly four blocks; this is the
witness count transported along `T27`. -/
public theorem T25x {W : Bitset} (hW : Atl W) : HasBlockCount W 4 := by
  obtain ⟨g, hg, hgeq⟩ := (T27 W).mp hW
  rw [← hgeq]
  exact HasBlockCount.image hg classSet_W0 T25

end UorAtlas.Closure

end
