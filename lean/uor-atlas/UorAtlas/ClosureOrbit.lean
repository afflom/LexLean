module

public import Init
public import UorAtlas.Closure

set_option autoImplicit false
set_option maxRecDepth 40000

public section

namespace UorAtlas.Closure

open UorAtlas.Prelude
open UorAtlas.Prelude.ListAux
open UorAtlas.Prelude.Linear
open UorAtlas.Roots
open UorAtlas.Blocks
open UorAtlas.Group
open UorAtlas.Census

/-! ## The `Aut` action preserves the three census predicates -/

@[expose] public def genBlockIndex (a : Fin 8) (i : Nat) : Nat :=
  blkFind (Bitset.toNat (actT (D20tab a) (blkAt i))) 13 0 3150

@[expose] public def genBlockOK (a : Fin 8) (i : Nat) : Bool :=
  decide (genBlockIndex a i < 3150)
    && decide (actT (D20tab a) (blkAt i) = blkAt (genBlockIndex a i))

set_option maxHeartbeats 4000000 in
public theorem genBlockAll :
    allFin (fun a : Fin 8 => allLt (fun i => genBlockOK a i) 3150) = true := by
  decide +kernel

public theorem D20_block (a : Fin 8) {B : Bitset} (hB : Blk B) :
    Blk (actP (D20 a) B) := by
  obtain ⟨i, hi, rfl⟩ := block_census_complete hB
  have hc := allLt_true _ _ (allFin_true _ genBlockAll a) i hi
  simp only [genBlockOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [show D20 a = tperm (D20tab a) (D20tab a) from rfl,
    ← actT_eq (D20tabOK a), hc.2]
  exact blkD16 hc.1

public theorem generator_block {s : Perm 120} (hs : s ∈ permsOf autGt)
    {B : Bitset} (hB : Blk B) : Blk (actP s B) := by
  rw [autGens_eq] at hs
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hs
  exact D20_block a hB

public theorem generator_inv_block {s : Perm 120} (hs : s ∈ permsOf autGt)
    {B : Bitset} (hB : Blk B) : Blk (actP s.inv B) := by
  rw [autGens_eq] at hs
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hs
  rw [D20_inv]
  exact D20_block a hB

public theorem aut_block {g : Perm 120} (hg : D21 g) {B : Bitset} (hB : Blk B) :
    Blk (actP g B) := by
  have key : ∀ p : Perm 120, Perm.Gen (permsOf autGt) p →
      ∀ C : Bitset, Blk C → Blk (actP p C) := by
    intro p hp
    induction hp with
    | one =>
        intro C hC
        rw [actP_one hC.1]
        exact hC
    | @step p s _ hs ih =>
        intro C hC
        rw [actP_comp]
        exact ih (actP s C) (generator_block hs hC)
    | @stepInv p s _ hs ih =>
        intro C hC
        rw [actP_comp]
        exact ih (actP s.inv C) (generator_inv_block hs hC)
  exact key g hg B hB

public theorem mem_actP_image_iff (g : Perm 120) (W : Bitset) (u : K) :
    (g.toFun u).val ∈ actP g W ↔ u.val ∈ W := by
  constructor
  · intro h
    obtain ⟨v, hv, he⟩ := (mem_actP g W _).mp h
    have hvu : v = u := Perm.toFun_injective (Fin.eq_of_val_eq he)
    rwa [hvu] at hv
  · intro h
    exact (mem_actP g W _).mpr ⟨u, h, rfl⟩

public theorem actP_union (g : Perm 120) (S T : Bitset) :
    actP g (Bitset.union S T) = Bitset.union (actP g S) (actP g T) := by
  refine Bitset.ext (fun i => ?_)
  simp only [mem_actP, Bitset.mem_union]
  constructor
  · rintro ⟨u, hu | hu, he⟩
    · exact Or.inl ⟨u, hu, he⟩
    · exact Or.inr ⟨u, hu, he⟩
  · rintro (⟨u, hu, he⟩ | ⟨u, hu, he⟩)
    · exact ⟨u, Or.inl hu, he⟩
    · exact ⟨u, Or.inr hu, he⟩

public theorem actP_inter (g : Perm 120) (S T : Bitset) :
    actP g (Bitset.inter S T) = Bitset.inter (actP g S) (actP g T) := by
  refine Bitset.ext (fun i => ?_)
  rw [Bitset.mem_inter]
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := (mem_actP g (Bitset.inter S T) i).mp h
    have hst := (Bitset.mem_inter S T u.val).mp hu
    exact ⟨(mem_actP g S i).mpr ⟨u, hst.1, he⟩,
      (mem_actP g T i).mpr ⟨u, hst.2, he⟩⟩
  · rintro ⟨hs, ht⟩
    obtain ⟨u, hu, hui⟩ := (mem_actP g S i).mp hs
    obtain ⟨v, hv, hvi⟩ := (mem_actP g T i).mp ht
    have huv : u = v := Perm.toFun_injective (Fin.eq_of_val_eq (hui.trans hvi.symm))
    exact (mem_actP g (Bitset.inter S T) i).mpr
      ⟨u, (Bitset.mem_inter S T u.val).mpr ⟨hu, huv ▸ hv⟩, hui⟩

public theorem actP_empty (g : Perm 120) : actP g Bitset.empty = Bitset.empty := by
  refine Bitset.ext (fun i => ⟨fun h => ?_, fun h => absurd h (Bitset.notMem_empty i)⟩)
  obtain ⟨u, hu, _⟩ := (mem_actP g Bitset.empty i).mp h
  exact absurd hu (Bitset.notMem_empty u.val)

public theorem D13_image_iff {g : Perm 120} (hg : D21 g) (u v : K) :
    D13 (g.toFun u) (g.toFun v) ↔ D13 u v := by
  rw [← A_eq_one_iff, ← A_eq_one_iff, T59p hg]

public theorem aut_frm {g : Perm 120} (hg : D21 g) {B C : Bitset} (h : Frm B C) :
    Frm (actP g B) (actP g C) := by
  refine ⟨aut_block hg h.1, aut_block hg h.2.1, ?_, ?_⟩
  · rw [← actP_inter, h.2.2.1, actP_empty]
  · intro u v hu hv hadj
    obtain ⟨u0, hu0, heu⟩ := (mem_actP g B u.val).mp hu
    obtain ⟨v0, hv0, hev⟩ := (mem_actP g C v.val).mp hv
    have eu : g.toFun u0 = u := Fin.eq_of_val_eq heu
    have ev : g.toFun v0 = v := Fin.eq_of_val_eq hev
    rw [← eu, ← ev, D13_image_iff hg] at hadj
    exact h.2.2.2 u0 v0 hu0 hv0 hadj

public theorem D14_image {g : Perm 120} (hg : D21 g) (W : Bitset) (u : K) :
    D14 (actP g W) (g.toFun u) = D14 W u := by
  show Vec.sumNat (fun v : K => if v.val ∈ actP g W then A v (g.toFun u) else 0) = _
  rw [← sumK_reindex g
    (fun v : K => if v.val ∈ actP g W then A v (g.toFun u) else 0)]
  refine Vec.sumNat_congr (fun v => ?_)
  have himg := mem_actP_image_iff g W v
  by_cases hv : v.val ∈ W
  · rw [if_pos (himg.mpr hv), if_pos hv, T59p hg v u]
  · rw [if_neg (fun h => hv (himg.mp h)), if_neg hv]

public theorem aut_tight {g : Perm 120} (hg : D21 g) {W : Bitset} (hW : D15 W) :
    D15 (actP g W) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    let u := g.invFun v
    have hgu : g.toFun u = v := g.right_inv v
    rw [← hgu, D14_image hg]
    apply hW.1 u
    exact (mem_actP_image_iff g W u).mp (hgu ▸ hv)
  · intro v hv
    let u := g.invFun v
    have hgu : g.toFun u = v := g.right_inv v
    rw [← hgu, D14_image hg]
    apply hW.2 u
    intro hu
    exact hv (hgu ▸ (mem_actP_image_iff g W u).mpr hu)

end UorAtlas.Closure

end
