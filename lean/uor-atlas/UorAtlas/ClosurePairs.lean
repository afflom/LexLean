module

public import Init
public import UorAtlas.ClosureOrbit

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

/-! ## Disjoint pairs of BlockFrames -/

@[expose] public def framePairOK (i j : Nat) : Prop :=
  i ∈ frameIds ∧ j ∈ frameIds ∧ i < j
    ∧ Bitset.inter (frameSupport i) (frameSupport j) = Bitset.empty

@[expose] public def frameSupportRows : List (Nat × Bitset) :=
  frameIds.map (fun i => (i, frameSupport i))

@[expose] public def atlasPairs : List (Nat × Nat) :=
  let rows := frameSupportRows
  rows.flatMap (fun p =>
    (rows.filter (fun q => decide (p.1 < q.1
      ∧ Bitset.inter p.2 q.2 = Bitset.empty))).map (fun q => (p.1, q.1)))

@[expose] public def pairSupport (p : Nat × Nat) : Bitset :=
  Bitset.union (frameSupport p.1) (frameSupport p.2)

@[expose] public def atlasSupports : List Bitset := atlasPairs.map pairSupport

public theorem mem_atlasPairs {i j : Nat} : (i, j) ∈ atlasPairs ↔ framePairOK i j := by
  simp only [atlasPairs, frameSupportRows, List.mem_flatMap, List.mem_map,
    List.mem_filter, decide_eq_true_eq, framePairOK]
  constructor
  · rintro ⟨p, ⟨k, hk, rfl⟩, q, ⟨⟨l, hl, rfl⟩, hij, hd⟩, he⟩
    cases he
    exact ⟨hk, hl, hij, hd⟩
  · rintro ⟨hi, hj, hij, hd⟩
    exact ⟨(i, frameSupport i), ⟨i, hi, rfl⟩,
      (j, frameSupport j), ⟨⟨j, hj, rfl⟩, hij, hd⟩, rfl⟩

public theorem mem_atlasSupports {W : Bitset} : W ∈ atlasSupports ↔
    ∃ i j, framePairOK i j ∧ W = pairSupport (i, j) := by
  rw [atlasSupports, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, p.2, mem_atlasPairs.mp hp, rfl⟩
  · rintro ⟨i, j, hp, rfl⟩
    exact ⟨(i, j), mem_atlasPairs.mpr hp, rfl⟩

@[expose] public def atlasPairRowCount (rows : List (Nat × Bitset))
    (p : Nat × Bitset) : Nat :=
  (rows.filter (fun q => decide (p.1 < q.1
    ∧ Bitset.inter p.2 q.2 = Bitset.empty))).length

@[expose] public def atlasPairCountTake (all : List (Nat × Bitset)) :
    List (Nat × Bitset) → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | p :: rows, n + 1 => atlasPairRowCount all p + atlasPairCountTake all rows n

public theorem atlasPairCountTake_nil (all : List (Nat × Bitset)) :
    ∀ n, atlasPairCountTake all [] n = 0 := by
  intro n
  cases n <;> rfl

public theorem atlasPairCountTake_append (all rows : List (Nat × Bitset)) (m n : Nat) :
    atlasPairCountTake all rows (m + n) =
      atlasPairCountTake all rows m + atlasPairCountTake all (rows.drop m) n := by
  induction m generalizing rows with
  | zero => simp [atlasPairCountTake]
  | succ m ih =>
      cases rows with
      | nil => simp [atlasPairCountTake_nil]
      | cons p rows =>
          rw [Nat.succ_add, atlasPairCountTake, atlasPairCountTake, List.drop_succ_cons,
            ih, Nat.add_assoc]

public theorem sum_rowCounts_eq_take (all rows : List (Nat × Bitset)) :
    (rows.map (atlasPairRowCount all)).sum =
      atlasPairCountTake all rows rows.length := by
  induction rows with
  | nil => rfl
  | cons p rows ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, atlasPairCountTake]
      rw [ih]

public theorem frameSupportRows_length : frameSupportRows.length = 1575 := by
  simp [frameSupportRows, frameIds_length]

public theorem atlasPairs_length_eq_count :
    atlasPairs.length = atlasPairCountTake frameSupportRows frameSupportRows 1575 := by
  rw [atlasPairs, List.length_flatMap]
  simp only [List.length_map]
  change (frameSupportRows.map (atlasPairRowCount frameSupportRows)).sum = _
  rw [sum_rowCounts_eq_take, frameSupportRows_length]

end UorAtlas.Closure

end
