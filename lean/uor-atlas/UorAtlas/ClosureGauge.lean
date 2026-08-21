module

public import Init
public import UorAtlas.ClosureOrbitTransport

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

/-! ## Universal gauge orders -/

public theorem gauge_conjugate_iff {g k : Perm 120} (hg : D21 g) :
    D28 (actP g W0) (conjugate g k) ↔ D28 W0 k := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hc : D21 (conjugate g.inv (conjugate g k)) :=
        Perm.Gen.comp_mem (Perm.Gen.inv_mem hg)
          (Perm.Gen.comp_mem h.1 hg)
      have he : conjugate g.inv (conjugate g k) = k := by
        simpa only [Perm.inv_inv] using conjugate_inv g.inv k
      rwa [he] at hc
    · have hw : actP g (actP k W0) = actP g W0 := by
        simpa only [conjugate, actP_comp, actP_inv g classSet_W0] using h.2
      exact actP_inj g (classSet_actP k W0) classSet_W0 hw
  · intro h
    refine ⟨Perm.Gen.comp_mem hg (Perm.Gen.comp_mem h.1 (Perm.Gen.inv_mem hg)), ?_⟩
    simp only [conjugate, actP_comp]
    rw [actP_inv g classSet_W0, h.2]

public theorem gauge_order_image {g : Perm 120} (hg : D21 g) :
    HasOrderP (D28 (actP g W0)) 4608 := by
  obtain ⟨L, hnd, hmem, hlen⟩ := gaugeOrderW0
  refine ⟨L.map (conjugate g), ?_, ?_, by rw [List.length_map, hlen]⟩
  · exact nodup_map_on (conjugate g) L hnd
      (fun a _ b _ he => conjugate_inj g he)
  · intro k
    constructor
    · intro hk
      obtain ⟨l, hl, he⟩ := List.mem_map.mp hk
      rw [← he]
      exact (gauge_conjugate_iff hg).mpr ((hmem l).mp hl)
    · intro hk
      let l := conjugate g.inv k
      have hl : D28 W0 l := by
        apply (gauge_conjugate_iff hg).mp
        rw [conjugate_inv]
        exact hk
      refine List.mem_map.mpr ⟨l, (hmem l).mpr hl, ?_⟩
      exact conjugate_inv g k

/-- `T29`.  Every AtlasInstance has gauge group order `4608`. -/
public theorem T29 {W : Bitset} (hW : Atl W) : HasOrderP (D28 W) 4608 := by
  obtain ⟨g, hg, he⟩ := (T27 W).mp hW
  rw [← he]
  exact gauge_order_image hg

/-- `T49`.  The section-10 gauge group is the same setwise stabiliser and has
order `4608` for every instance. -/
public theorem T49 {W : Bitset} (hW : Atl W) : HasOrderP (D28 W) 4608 := T29 hW

/-- `T60`.  Reading the same stabiliser inside `Aut(Gamma)` does not change its
order, because `T59a` identifies graph automorphisms with `Aut`. -/
public theorem T60 {W : Bitset} (hW : Atl W) :
    HasOrderP (fun g : Perm 120 => AutA g ∧ actP g W = W) 4608 := by
  obtain ⟨L, hnd, hmem, hlen⟩ := T29 hW
  exact ⟨L, hnd, fun g => (hmem g).trans ⟨
    fun h => ⟨autA_of_D21 h.1, h.2⟩,
    fun h => ⟨autA_gen h.1, h.2⟩⟩, hlen⟩

/-- `T32`.  For the exhibited presentation, the kernel of the block action
has order `576`. -/
public theorem T32 : HasOrderP (D29 Blocks.blkSet W0) 576 := by
  obtain ⟨L, hnd, hmem, hlen⟩ := T39p
  exact ⟨L, hnd, fun g => (hmem g).trans (stabPres_iff_D29 g), hlen⟩

/-- `T51`.  The kernel count in the section-10 notation. -/
public theorem T51 : HasOrderP (D29 Blocks.blkSet W0) 576 := T32

/-! ## Faithfulness of the kernel on each block -/

/-- Pointwise fixation of every class in a block. -/
@[expose] public def FixesBlock (B : Bitset) (g : Perm 120) : Prop :=
  ∀ u : K, u.val ∈ B → g.toFun u = u

/-- Four Schreier chains for the kernel, each based wholly inside one of the
four blocks.  Their orbit lengths are respectively `12,3,8,2` (or
`12,3,2,8`), so fixation of the chosen block forces every chain level to
descend through its trivial final stabiliser. -/
@[expose] public def kerFaithSpec (a : Fin 4) : List (Nat × List (List Nat)) :=
  if a = 0 then
    [(0, [[0], [6], [3, 0, 2], [5, 2, 4]]),
     (1, [[0], [4], [6], [3, 0, 2]]), (2, [[5, 2, 0]]), (4, [])]
  else if a = 1 then
    [(6, [[2], [1, 2, 0], [1, 4, 0], [7, 0, 6]]),
     (20, [[0], [2], [6], [5, 2, 4]]), (32, [[0], [2], [6]]), (56, [])]
  else if a = 2 then
    [(7, [[2], [1, 2, 0], [1, 4, 0], [7, 0, 6]]),
     (21, [[0], [2], [6], [5, 2, 4]]), (33, [[0], [2], [6]]), (63, [])]
  else
    [(44, [[0], [6], [3, 0, 2], [5, 2, 4]]),
     (45, [[0], [4], [6], [3, 0, 2]]), (46, [[5, 2, 0]]), (48, [])]

set_option maxHeartbeats 4000000 in
public theorem kerFaithChain (a : Fin 4) :
    chainCheck kerGt (mkChain kerGt (kerFaithSpec a)) = true := by
  refine fin4 (P := fun a => chainCheck kerGt (mkChain kerGt (kerFaithSpec a)) = true)
    ?_ ?_ ?_ ?_ a <;> decide +kernel

public theorem kerFaithBases : allFin (fun a : Fin 4 =>
    (kerFaithSpec a).all (fun p => decide (p.1 ∈ Blocks.blkSet a))) = true := by
  decide +kernel

public theorem kernel_faithful_on_witness_block (a : Fin 4) {g : Perm 120}
    (hg : Perm.Gen (permsOf kerGt) g) (hfix : FixesBlock (Blocks.blkSet a) g) :
    g = Perm.one 120 := by
  let f : Nat → Nat := fun i => (g.toFun (fin120 i)).val
  have hagree : Agree f g := by
    intro i
    show (g.toFun i).val = (g.toFun (fin120 i.val)).val
    rw [show fin120 i.val = i from Fin.eq_of_val_eq (fin120_val i.isLt)]
  have hm : memChain (mkChain kerGt (kerFaithSpec a)) f = true :=
    ((mkChain_spec (kerFaithSpec a) kerGt kerGt_ok (kerFaithChain a)).1 f g hagree).mpr hg
  have hlt : ∀ i, i < 120 → f i < 120 := fun i _ => (g.toFun (fin120 i)).isLt
  have hbases : ∀ l ∈ mkChain kerGt (kerFaithSpec a), f l.bp = l.bp := by
    intro l hl
    obtain ⟨p, hp, hbp⟩ := mkChain_bp (kerFaithSpec a) kerGt l hl
    have hmem : p.1 ∈ Blocks.blkSet a := of_decide_eq_true
      (List.all_eq_true.mp (allFin_true _ kerFaithBases a) p hp)
    have hpLt : p.1 < 120 := by
      rw [← hbp]
      exact mkChain_bp_lt (kerFaithSpec a) kerGt (kerFaithChain a) l hl
    have he := congrArg Fin.val (hfix ⟨p.1, hpLt⟩ hmem)
    rw [hbp]
    show (g.toFun (fin120 p.1)).val = p.1
    rw [show fin120 p.1 = (⟨p.1, hpLt⟩ : Fin 120) from
      Fin.eq_of_val_eq (fin120_val hpLt)]
    exact he
  have hall := memChain_fix (kerFaithSpec a) kerGt kerGt_ok (kerFaithChain a)
    f hlt hbases hm
  exact Perm.ext (fun i => Fin.eq_of_val_eq (by
    show (g.toFun i).val = i.val
    have hi := hall i.val i.isLt
    change (g.toFun (fin120 i.val)).val = i.val at hi
    rw [show fin120 i.val = i from Fin.eq_of_val_eq (fin120_val i.isLt)] at hi
    exact hi))

public theorem kernel_faithful_on_witness_presentation (a : Fin 4) {g : Perm 120}
    (hg : D29 Blocks.blkSet W0 g)
    (hfix : FixesBlock (Blocks.blkSet a) g) : g = Perm.one 120 := by
  apply kernel_faithful_on_witness_block a
  · exact (stabPres_eq g).mp ((stabPres_iff_D29 g).mpr hg)
  · exact hfix

end UorAtlas.Closure

end
