module

public import Init
public import UorAtlas.ClosurePairComplete

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

/-! ## Orbit cardinality without enumerating `348364800` automorphisms -/

@[expose] public def orbitImages (L : List (Perm 120)) : List Bitset :=
  dedup (L.map (fun g => actP g W0))

public theorem mem_orbitImages {L : List (Perm 120)} {W : Bitset} :
    W ∈ orbitImages L ↔ ∃ g ∈ L, actP g W0 = W := by
  rw [orbitImages, mem_dedup, List.mem_map]

public theorem orbitImages_nodup (L : List (Perm 120)) : (orbitImages L).Nodup :=
  nodup_dedup

public theorem action_fibre_count {L S : List (Perm 120)}
    (hLnd : L.Nodup) (hL : ∀ g, g ∈ L ↔ D21 g)
    (hSnd : S.Nodup) (hS : ∀ g, g ∈ S ↔ D21 g ∧ actP g W0 = W0)
    (hSlen : S.length = 4608) {W : Bitset} (hW : W ∈ orbitImages L) :
    L.countP (fun g => decide (actP g W0 = W)) = 4608 := by
  obtain ⟨t, htL, htW⟩ := mem_orbitImages.mp hW
  have ht : D21 t := (hL t).mp htL
  have hlen : (S.map (fun s => t.comp s)).length = 4608 := by
    rw [List.length_map, hSlen]
  rw [List.countP_eq_length_filter, ← hlen]
  apply length_eq_of_mem_iff (List.Pairwise.filter _ hLnd)
  · exact List.Pairwise.map _
      (fun a b hab he => hab (Perm.comp_left_cancel he)) hSnd
  · intro g
    rw [List.mem_filter, List.mem_map]
    constructor
    · rintro ⟨hgL, hgW⟩
      have hg : D21 g := (hL g).mp hgL
      let s := t.inv.comp g
      have hs : D21 s := Perm.Gen.comp_mem (Perm.Gen.inv_mem ht) hg
      have hsW : actP s W0 = W0 := by
        show actP (t.inv.comp g) W0 = W0
        rw [actP_comp, of_decide_eq_true hgW, ← htW, ← actP_comp,
          Perm.inv_comp, actP_one classSet_W0]
      refine ⟨s, (hS s).mpr ⟨hs, hsW⟩, ?_⟩
      show t.comp (t.inv.comp g) = g
      rw [← Perm.comp_assoc, Perm.comp_inv, Perm.one_comp]
    · rintro ⟨s, hsS, rfl⟩
      have hs := (hS s).mp hsS
      refine ⟨(hL (t.comp s)).mpr (Perm.Gen.comp_mem ht hs.1), decide_eq_true ?_⟩
      rw [actP_comp, hs.2, htW]

/-- The `Aut` orbit of the witness contains exactly `75600` class sets.  The
proof partitions the certified `348364800`-element group list into fibres of
size `4608`; neither list is evaluated. -/
public theorem orbit_count : ∃ O : List Bitset,
    O.Nodup ∧ O.length = 75600
      ∧ ∀ W : Bitset, W ∈ O ↔ ∃ g : Perm 120, D21 g ∧ actP g W0 = W := by
  obtain ⟨L, hLnd, hLmem, hLlen⟩ := T28
  obtain ⟨S, hSnd, hSmem, hSlen⟩ := gaugeOrderWitness
  have hL : ∀ g, g ∈ L ↔ D21 g := by
    intro g
    exact hLmem g
  have hS : ∀ g, g ∈ S ↔ D21 g ∧ actP g W0 = W0 := by
    intro g
    rw [hSmem g, D28, W0_eq]
  let O := orbitImages L
  have hcover : ∀ g ∈ L, actP g W0 ∈ O := by
    intro g hg
    exact mem_orbitImages.mpr ⟨g, hg, rfl⟩
  have hpartition := length_eq_sum_fibres (fun g : Perm 120 => actP g W0)
    (orbitImages_nodup L) hcover
  have hfibre : ∀ W ∈ O,
      L.countP (fun g => decide (actP g W0 = W)) = 4608 := by
    intro W hW
    exact action_fibre_count hLnd hL hSnd hS hSlen hW
  rw [List.map_congr_left hfibre, sum_map_const, hLlen] at hpartition
  have hOlen : O.length = 75600 := by omega
  refine ⟨O, orbitImages_nodup L, hOlen, fun W => ?_⟩
  rw [mem_orbitImages]
  constructor
  · rintro ⟨g, hg, he⟩
    exact ⟨g, (hL g).mp hg, he⟩
  · rintro ⟨g, hg, he⟩
    exact ⟨g, (hL g).mpr hg, he⟩

end UorAtlas.Closure

end
