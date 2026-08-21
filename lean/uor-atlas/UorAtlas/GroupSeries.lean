module

public import Init
public import UorAtlas.Group

/-!
# The gauge quotient and its characteristic series

The witness gauge group is finite through the checked Schreier chain in
`UorAtlas.Group`.  This module identifies its eight-element block action,
constructs a dihedral complement, and checks the commutator generators used by
the derived and lower-central series.
-/

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

public section

namespace UorAtlas.Closure

open UorAtlas.Prelude
open UorAtlas.Prelude.ListAux
open UorAtlas.Roots
open UorAtlas.Blocks
open UorAtlas.Group

@[expose] public def conjugate (g k : Perm 120) : Perm 120 :=
  g.comp (k.comp g.inv)

public theorem conjugate_inj (g : Perm 120) {k l : Perm 120}
    (h : conjugate g k = conjugate g l) : k = l := by
  apply Perm.ext
  intro i
  have hi := congrArg (fun p : Perm 120 => p.toFun (g.toFun i)) h
  simp only [conjugate, Perm.comp_apply, Perm.inv_apply, Perm.left_inv] at hi
  exact g.toFun_injective hi

public theorem conjugate_inv (g k : Perm 120) :
    conjugate g (conjugate g.inv k) = k := by
  apply Perm.ext
  intro i
  simp only [conjugate, Perm.comp_apply, Perm.inv_apply, Perm.inv_inv,
    Perm.right_inv]

public theorem cosP_gen (i : Nat) : Perm.Gen (permsOf stabGt) (cosP i) := by
  show Perm.Gen (permsOf stabGt) (tpermP (evalT stabGt (cosWords.getD i [])))
  rw [← evalP_permsOf stabGt_ok]
  exact gen_evalP _ _

public theorem cosP_gauge (i : Nat) : D28 W0 (cosP i) :=
  stabGen_gauge (cosP_gen i)

@[expose] public def cosActionDistinctOK : Bool :=
  allLt (fun i => allLt (fun j => decide
    (D28a Blocks.blkSet (cosP i) = D28a Blocks.blkSet (cosP j) → i = j)) 8) 8

set_option maxHeartbeats 4000000 in
public theorem cosActionDistinctCert : cosActionDistinctOK = true := by decide +kernel

public theorem cosActionDistinct {i j : Nat} (hi : i < 8) (hj : j < 8)
    (h : D28a Blocks.blkSet (cosP i) = D28a Blocks.blkSet (cosP j)) : i = j := by
  exact (of_decide_eq_true
    (allLt_true _ _ (allLt_true _ _ cosActionDistinctCert i hi) j hj)) h

/-- `T31`.  The block action has exactly eight images. -/
public theorem T31 :
    (∀ i : Nat, i < 8 → D28 W0 (cosP i))
      ∧ (∀ i j : Nat, i < 8 → j < 8 → i ≠ j →
        D28a Blocks.blkSet (cosP i) ≠ D28a Blocks.blkSet (cosP j))
      ∧ (∀ g : Perm 120, D28 W0 g → ∃ i : Nat, i < 8 ∧
        ∃ k : Perm 120, Perm.Gen (permsOf kerGt) k ∧ g = k.comp (cosP i)) := by
  refine ⟨fun i _ => cosP_gauge i,
    fun i j hi hj hij he => hij (cosActionDistinct hi hj he), ?_⟩
  intro g hg
  exact gauge_coset ((gauge_eq g).mp hg)

@[expose] public def cosList : List (Perm 120) := (List.range 8).map cosP

public theorem nodup_map_inj {α β : Type} (f : α → β) : ∀ l : List α, l.Nodup →
    (∀ x, x ∈ l → ∀ y, y ∈ l → f x = f y → x = y) → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; exact List.nodup_nil
  | cons x xs ih =>
    intro hnd hinj
    have hn := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨?_, ih hn.2 ?_⟩
    · intro hm
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
      have hyx := hinj y (List.mem_cons_of_mem _ hy) x (List.mem_cons_self ..) he
      exact hn.1 (hyx ▸ hy)
    · intro y hy z hz he
      exact hinj y (List.mem_cons_of_mem _ hy) z (List.mem_cons_of_mem _ hz) he

public theorem cosList_nodup : cosList.Nodup := by
  apply nodup_map_inj cosP (List.range 8) List.nodup_range
  intro i hi j hj he
  exact cosActionDistinct (List.mem_range.mp hi) (List.mem_range.mp hj)
    (congrArg (D28a Blocks.blkSet) he)

public theorem cosList_length : cosList.length = 8 := by simp [cosList]

public theorem mem_cosList {c : Perm 120} : c ∈ cosList ↔
    ∃ i : Nat, i < 8 ∧ c = cosP i := by
  rw [cosList, List.mem_map]
  exact ⟨fun ⟨i, hi, he⟩ => ⟨i, List.mem_range.mp hi, he.symm⟩,
    fun ⟨i, hi, he⟩ => ⟨i, List.mem_range.mpr hi, he.symm⟩⟩

@[expose] public def cosIndex (p : Perm 120) : Nat :=
  ((List.range 8).findIdx? (fun i => decide (p = cosP i))).getD 0

@[expose] public def cosMulOK (i j : Nat) : Bool :=
  decide (cosIndex ((cosP i).comp (cosP j)) < 8)
    && decide ((cosP i).comp (cosP j) = cosP (cosIndex ((cosP i).comp (cosP j))))

@[expose] public def cosInvOK (i : Nat) : Bool :=
  decide (cosIndex (cosP i).inv < 8)
    && decide ((cosP i).inv = cosP (cosIndex (cosP i).inv))

set_option maxHeartbeats 4000000 in
public theorem cosSubgroupCert :
    allLt (fun i => allLt (fun j => cosMulOK i j) 8) 8 = true
      ∧ allLt cosInvOK 8 = true := by decide +kernel

public theorem cosList_mul {a b : Perm 120} (ha : a ∈ cosList) (hb : b ∈ cosList) :
    a.comp b ∈ cosList := by
  obtain ⟨i, hi, rfl⟩ := mem_cosList.mp ha
  obtain ⟨j, hj, rfl⟩ := mem_cosList.mp hb
  have hc := allLt_true _ _ (allLt_true _ _ cosSubgroupCert.1 i hi) j hj
  simp only [cosMulOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact mem_cosList.mpr ⟨cosIndex ((cosP i).comp (cosP j)), hc.1, hc.2⟩

public theorem cosList_inv {a : Perm 120} (ha : a ∈ cosList) : a.inv ∈ cosList := by
  obtain ⟨i, hi, rfl⟩ := mem_cosList.mp ha
  have hc := allLt_true _ _ cosSubgroupCert.2 i hi
  simp only [cosInvOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact mem_cosList.mpr ⟨cosIndex (cosP i).inv, hc.1, hc.2⟩

public theorem cosList_one : Perm.one 120 ∈ cosList :=
  mem_cosList.mpr ⟨0, by decide, cosP_zero.symm⟩

@[expose] public def d8Rotation : Perm 120 := cosP 3
@[expose] public def d8Reflection : Perm 120 := cosP 1

/-- `T50`.  The eight block actions form the displayed dihedral complement. -/
public theorem T50 :
    cosList.Nodup ∧ cosList.length = 8 ∧ Perm.one 120 ∈ cosList
      ∧ (∀ a b, a ∈ cosList → b ∈ cosList → a.comp b ∈ cosList)
      ∧ (∀ a, a ∈ cosList → a.inv ∈ cosList)
      ∧ d8Rotation.comp d8Rotation ≠ Perm.one 120
      ∧ (d8Rotation.comp d8Rotation).comp
          (d8Rotation.comp d8Rotation) = Perm.one 120
      ∧ d8Reflection.comp d8Reflection = Perm.one 120
      ∧ d8Reflection.comp (d8Rotation.comp d8Reflection) = d8Rotation.inv := by
  refine ⟨cosList_nodup, cosList_length, cosList_one,
    (fun a b => cosList_mul (a := a) (b := b)),
    (fun a => cosList_inv (a := a)),
    ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## Exact commutator closures -/

@[expose] public def commutator (g h : Perm 120) : Perm 120 :=
  g.comp (h.comp (g.inv.comp h.inv))

@[expose] public def SubgroupPred (P : Perm 120 → Prop) : Prop :=
  P (Perm.one 120)
    ∧ (∀ g h, P g → P h → P (g.comp h))
    ∧ (∀ g, P g → P g.inv)

@[expose] public def NormalIn (G H : Perm 120 → Prop) : Prop :=
  ∀ g h, G g → H h → H (conjugate g h)

/-- The subgroup generated by commutators with left entries in `G` and right
entries in `H`.  Keeping this as an inductive closure makes "derived" and
"lower central" exact predicates rather than names assigned to computed
subgroups. -/
public inductive CommClosure (G H : Perm 120 → Prop) : Perm 120 → Prop where
  | one : CommClosure G H (Perm.one 120)
  | comm {g h : Perm 120} : G g → H h → CommClosure G H (commutator g h)
  | comp {g h : Perm 120} : CommClosure G H g → CommClosure G H h →
      CommClosure G H (g.comp h)
  | inv {g : Perm 120} : CommClosure G H g → CommClosure G H g.inv

@[expose] public def DerivedOf (G D : Perm 120 → Prop) : Prop :=
  ∀ g, D g ↔ CommClosure G G g

@[expose] public def LowerCentralStep (G H K : Perm 120 → Prop) : Prop :=
  ∀ g, K g ↔ CommClosure G H g

public theorem commutator_one_left (g : Perm 120) :
    commutator (Perm.one 120) g = Perm.one 120 := by
  simpa only [commutator, Perm.one_inv, Perm.one_comp] using Perm.comp_inv g

public theorem commutator_one_right (g : Perm 120) :
    commutator g (Perm.one 120) = Perm.one 120 := by
  simpa only [commutator, Perm.one_inv, Perm.one_comp, Perm.comp_one] using Perm.comp_inv g

public theorem conjugate_one (g : Perm 120) :
    conjugate g (Perm.one 120) = Perm.one 120 := by
  simpa only [conjugate, Perm.one_comp] using Perm.comp_inv g

public theorem conjugate_comp (g a b : Perm 120) :
    conjugate g (a.comp b) = (conjugate g a).comp (conjugate g b) := by
  apply Perm.ext
  intro i
  simp only [conjugate, Perm.comp_apply, Perm.inv_apply, Perm.left_inv]

public theorem conjugate_group_inv (g a : Perm 120) :
    conjugate g a.inv = (conjugate g a).inv := by
  apply Perm.ext
  intro i
  simp only [conjugate, Perm.comp_apply, Perm.inv_comp_distrib, Perm.inv_apply,
    Perm.inv_inv]

public theorem conjugate_outer_comp (a b h : Perm 120) :
    conjugate (a.comp b) h = conjugate a (conjugate b h) := by
  apply Perm.ext
  intro i
  simp only [conjugate, Perm.comp_apply, Perm.inv_comp_distrib, Perm.inv_apply]

public theorem commutator_comp_left (a b c : Perm 120) :
    commutator (a.comp b) c =
      (conjugate a (commutator b c)).comp (commutator a c) := by
  apply Perm.ext
  intro i
  simp only [commutator, conjugate, Perm.comp_apply, Perm.inv_comp_distrib,
    Perm.inv_apply, Perm.left_inv]

public theorem commutator_comp_right (a b c : Perm 120) :
    commutator a (b.comp c) =
      (commutator a b).comp (conjugate b (commutator a c)) := by
  apply Perm.ext
  intro i
  simp only [commutator, conjugate, Perm.comp_apply, Perm.inv_comp_distrib,
    Perm.inv_apply, Perm.left_inv]

public theorem commutator_inv_left (a b : Perm 120) :
    commutator a.inv b = conjugate a.inv (commutator a b).inv := by
  apply Perm.ext
  intro i
  simp only [commutator, conjugate, Perm.comp_apply, Perm.inv_comp_distrib,
    Perm.inv_apply, Perm.inv_inv, Perm.left_inv]

public theorem commutator_inv_right (a b : Perm 120) :
    commutator a b.inv = conjugate b.inv (commutator a b).inv := by
  apply Perm.ext
  intro i
  simp only [commutator, conjugate, Perm.comp_apply, Perm.inv_comp_distrib,
    Perm.inv_apply, Perm.inv_inv, Perm.left_inv]

public theorem gen_subgroupPred (gt : List (Perm 120)) : SubgroupPred (Perm.Gen gt) :=
  ⟨Perm.Gen.one, fun _ _ => Perm.Gen.comp_mem, fun _ => Perm.Gen.inv_mem⟩

public theorem commClosure_subgroup (G H : Perm 120 → Prop) :
    SubgroupPred (CommClosure G H) :=
  ⟨CommClosure.one, fun _ _ => CommClosure.comp, fun _ => CommClosure.inv⟩

public theorem generated_normal_of_letters {outer inner : List (Perm 120)}
    (_hsub : ∀ s, s ∈ inner → Perm.Gen outer s)
    (hletters : ∀ s, s ∈ outer → ∀ t, t ∈ inner →
      Perm.Gen inner (conjugate s t) ∧ Perm.Gen inner (conjugate s.inv t)) :
    NormalIn (Perm.Gen outer) (Perm.Gen inner) := by
  have byLetter : ∀ s, s ∈ outer → ∀ h, Perm.Gen inner h →
      Perm.Gen inner (conjugate s h) ∧ Perm.Gen inner (conjugate s.inv h) := by
    intro s hs h hh
    induction hh with
    | one =>
      rw [conjugate_one, conjugate_one]
      exact ⟨Perm.Gen.one, Perm.Gen.one⟩
    | @step p t hp ht ih =>
      rw [conjugate_comp, conjugate_comp]
      exact ⟨Perm.Gen.comp_mem ih.1 (hletters s hs t ht).1,
        Perm.Gen.comp_mem ih.2 (hletters s hs t ht).2⟩
    | @stepInv p t hp ht ih =>
      rw [conjugate_comp, conjugate_comp, conjugate_group_inv, conjugate_group_inv]
      exact ⟨Perm.Gen.comp_mem ih.1 (Perm.Gen.inv_mem (hletters s hs t ht).1),
        Perm.Gen.comp_mem ih.2 (Perm.Gen.inv_mem (hletters s hs t ht).2)⟩
  intro g h hg
  induction hg generalizing h with
  | one => intro hh; simpa only [conjugate, Perm.one_inv, Perm.one_comp,
      Perm.comp_one] using hh
  | @step p s hp hs ih =>
    intro hh
    rw [conjugate_outer_comp]
    exact ih _ (byLetter s hs h hh).1
  | @stepInv p s hp hs ih =>
    intro hh
    rw [conjugate_outer_comp]
    exact ih _ (byLetter s hs h hh).2

public theorem generated_mixed_commutators_of_letters
    {outer middle target : List (Perm 120)}
    (hmiddle : ∀ s, s ∈ middle → Perm.Gen outer s)
    (hnormal : NormalIn (Perm.Gen outer) (Perm.Gen target))
    (hcomm : ∀ s, s ∈ outer → ∀ t, t ∈ middle →
      Perm.Gen target (commutator s t)) :
    ∀ g h, Perm.Gen outer g → Perm.Gen middle h →
      Perm.Gen target (commutator g h) := by
  have right (s : Perm 120) (hs : s ∈ outer) :
      ∀ h, Perm.Gen middle h → Perm.Gen target (commutator s h) := by
    intro h hh
    induction hh with
    | one => rw [commutator_one_right]; exact Perm.Gen.one
    | @step p t hp ht ih =>
      rw [commutator_comp_right]
      exact Perm.Gen.comp_mem ih
        (hnormal p (commutator s t) (gen_sub (fun q hq => hmiddle q hq) hp)
          (hcomm s hs t ht))
    | @stepInv p t hp ht ih =>
      rw [commutator_comp_right, commutator_inv_right]
      exact Perm.Gen.comp_mem ih
        (hnormal p (conjugate t.inv (commutator s t).inv)
          (gen_sub (fun q hq => hmiddle q hq) hp)
          (hnormal t.inv (commutator s t).inv
            (Perm.Gen.inv_mem (hmiddle t ht))
            (Perm.Gen.inv_mem (hcomm s hs t ht))))
  intro g h hg hh
  induction hg with
  | one => rw [commutator_one_left]; exact Perm.Gen.one
  | @step p s hp hs ih =>
    rw [commutator_comp_left]
    exact Perm.Gen.comp_mem (hnormal p (commutator s h) hp (right s hs h hh)) ih
  | @stepInv p s hp hs ih =>
    rw [commutator_comp_left, commutator_inv_left]
    exact Perm.Gen.comp_mem
      (hnormal p (conjugate s.inv (commutator s h).inv) hp
        (hnormal s.inv (commutator s h).inv
          (Perm.Gen.inv_mem (Perm.Gen.mem_gen hs))
          (Perm.Gen.inv_mem (right s hs h hh)))) ih

public theorem exact_commClosure_of_generators
    {outer middle target : List (Perm 120)}
    (hall : ∀ g h, Perm.Gen outer g → Perm.Gen middle h →
      Perm.Gen target (commutator g h))
    (hgens : ∀ s, s ∈ target → CommClosure (Perm.Gen outer) (Perm.Gen middle) s) :
    LowerCentralStep (Perm.Gen outer) (Perm.Gen middle) (Perm.Gen target) := by
  intro g
  constructor
  · intro hg
    induction hg with
    | one => exact CommClosure.one
    | step _ hs ih => exact CommClosure.comp ih (hgens _ hs)
    | stepInv _ hs ih => exact CommClosure.comp ih (CommClosure.inv (hgens _ hs))
  · intro hg
    induction hg with
    | one => exact Perm.Gen.one
    | comm hG hH => exact hall _ _ hG hH
    | @comp x y hx hy ihx ihy => exact Perm.Gen.comp_mem ihx ihy
    | @inv x hx ih => exact Perm.Gen.inv_mem ih

/-! ### Packed certificates for the derived series -/

@[expose] public def pairMul (a b : Nat × Nat) : Nat × Nat :=
  (mulT a.1 b.1, mulT b.2 a.2)

@[expose] public def pairInv (a : Nat × Nat) : Nat × Nat := (a.2, a.1)

@[expose] public def pairConjugate (a b : Nat × Nat) : Nat × Nat :=
  pairMul a (pairMul b (pairInv a))

@[expose] public def pairCommutator (a b : Nat × Nat) : Nat × Nat :=
  pairMul a (pairMul b (pairMul (pairInv a) (pairInv b)))

public theorem pairMul_perm {a b : Nat × Nat}
    (ha : tabOK a.1 a.2 = true) (hb : tabOK b.1 b.2 = true) :
    tpermP (pairMul a b) = (tpermP a).comp (tpermP b) :=
  tperm_mul ha hb

public theorem pairInv_perm {a : Nat × Nat} (ha : tabOK a.1 a.2 = true) :
    tpermP (pairInv a) = (tpermP a).inv := tperm_swap ha

public theorem pairConjugate_perm {a b : Nat × Nat}
    (ha : tabOK a.1 a.2 = true) (hb : tabOK b.1 b.2 = true) :
    tpermP (pairConjugate a b) = conjugate (tpermP a) (tpermP b) := by
  have hab : tabOK (pairMul b (pairInv a)).1 (pairMul b (pairInv a)).2 = true :=
    tabOK_mul hb (tabOK_swap ha)
  calc
    tpermP (pairConjugate a b) =
        (tpermP a).comp (tpermP (pairMul b (pairInv a))) :=
      pairMul_perm (a := a) (b := pairMul b (pairInv a)) ha hab
    _ = (tpermP a).comp ((tpermP b).comp (tpermP (pairInv a))) := by
      rw [pairMul_perm (a := b) (b := pairInv a) hb (tabOK_swap ha)]
    _ = (tpermP a).comp ((tpermP b).comp (tpermP a).inv) := by
      rw [pairInv_perm (a := a) ha]
    _ = conjugate (tpermP a) (tpermP b) := rfl

public theorem pairCommutator_perm {a b : Nat × Nat}
    (ha : tabOK a.1 a.2 = true) (hb : tabOK b.1 b.2 = true) :
    tpermP (pairCommutator a b) = commutator (tpermP a) (tpermP b) := by
  have hinv : tabOK (pairMul (pairInv a) (pairInv b)).1
      (pairMul (pairInv a) (pairInv b)).2 = true :=
    tabOK_mul (tabOK_swap ha) (tabOK_swap hb)
  have htail : tabOK (pairMul b (pairMul (pairInv a) (pairInv b))).1
      (pairMul b (pairMul (pairInv a) (pairInv b))).2 = true :=
    tabOK_mul hb hinv
  calc
    tpermP (pairCommutator a b) =
        (tpermP a).comp
          (tpermP (pairMul b (pairMul (pairInv a) (pairInv b)))) :=
      pairMul_perm (a := a)
        (b := pairMul b (pairMul (pairInv a) (pairInv b))) ha htail
    _ = (tpermP a).comp ((tpermP b).comp
          (tpermP (pairMul (pairInv a) (pairInv b)))) := by
      rw [pairMul_perm (a := b) (b := pairMul (pairInv a) (pairInv b)) hb hinv]
    _ = (tpermP a).comp ((tpermP b).comp
          ((tpermP (pairInv a)).comp (tpermP (pairInv b)))) := by
      rw [pairMul_perm (a := pairInv a) (b := pairInv b)
        (tabOK_swap ha) (tabOK_swap hb)]
    _ = (tpermP a).comp ((tpermP b).comp
          ((tpermP a).inv.comp (tpermP b).inv)) := by
      rw [pairInv_perm (a := a) ha, pairInv_perm (a := b) hb]
    _ = commutator (tpermP a) (tpermP b) := rfl

@[expose] public def derivedOneWords : List (List Nat) :=
  [[0, 2, 1, 3], [0, 4, 1, 5], [0, 6, 1, 7], [4, 6, 5, 7]]

@[expose] public def derivedOneGt : List (Nat × Nat) :=
  derivedOneWords.map (evalT stabGt)

@[expose] public def derivedOneSpec : List (Nat × List (List Nat)) :=
  [(8, [[0], [3, 6, 4, 6, 5, 2, 6], [2, 5, 6, 5, 6, 5, 2, 6]]), (2, [])]

@[expose] public def derivedTwoWords : List (List Nat) :=
  [[0, 2, 1, 3], [0, 6, 1, 7], [2, 4, 3, 5], [4, 6, 5, 7]]

@[expose] public def derivedTwoGt : List (Nat × Nat) :=
  derivedTwoWords.map (evalT derivedOneGt)

@[expose] public def derivedTwoSpec : List (Nat × List (List Nat)) :=
  [(8, [[5, 0, 4]]), (2, [])]

@[expose] public def derivedThreeWords : List (List Nat) :=
  [[0, 4, 1, 5], [0, 6, 1, 7], [2, 4, 3, 5], [4, 6, 5, 7]]

@[expose] public def derivedThreeGt : List (Nat × Nat) :=
  derivedThreeWords.map (evalT derivedTwoGt)

@[expose] public def derivedThreeSpec : List (Nat × List (List Nat)) :=
  [(8, [[0]]), (2, [])]

public theorem derivedOneGt_ok : TabsOK derivedOneGt :=
  tabsOK_nextGt stabGt_ok derivedOneWords

public theorem derivedTwoGt_ok : TabsOK derivedTwoGt :=
  tabsOK_nextGt derivedOneGt_ok derivedTwoWords

public theorem derivedThreeGt_ok : TabsOK derivedThreeGt :=
  tabsOK_nextGt derivedTwoGt_ok derivedThreeWords

set_option maxHeartbeats 4000000 in
public theorem derivedOneChain :
    chainCheck derivedOneGt (mkChain derivedOneGt derivedOneSpec) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem derivedTwoChain :
    chainCheck derivedTwoGt (mkChain derivedTwoGt derivedTwoSpec) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem derivedThreeChain :
    chainCheck derivedThreeGt (mkChain derivedThreeGt derivedThreeSpec) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem derivedChainLengths :
    chainLen (mkChain derivedOneGt derivedOneSpec) = 576
      ∧ chainLen (mkChain derivedTwoGt derivedTwoSpec) = 144
      ∧ chainLen (mkChain derivedThreeGt derivedThreeSpec) = 16 := by
  decide +kernel

public theorem derivedOneOrder : HasOrder (permsOf derivedOneGt) 576 := by
  have h := (mkChain_spec derivedOneSpec derivedOneGt derivedOneGt_ok derivedOneChain).2
  rwa [derivedChainLengths.1] at h

public theorem derivedTwoOrder : HasOrder (permsOf derivedTwoGt) 144 := by
  have h := (mkChain_spec derivedTwoSpec derivedTwoGt derivedTwoGt_ok derivedTwoChain).2
  rwa [derivedChainLengths.2.1] at h

public theorem derivedThreeOrder : HasOrder (permsOf derivedThreeGt) 16 := by
  have h := (mkChain_spec derivedThreeSpec derivedThreeGt derivedThreeGt_ok
    derivedThreeChain).2
  rwa [derivedChainLengths.2.2] at h

@[expose] public def chainMemberCheck (gt : List (Nat × Nat))
    (spec : List (Nat × List (List Nat))) (q : Nat × Nat) : Bool :=
  memChain (mkChain gt spec) (fun i => ap q.1 i)

public theorem chainMember_of_check {gt : List (Nat × Nat)}
    {spec : List (Nat × List (List Nat))} {q : Nat × Nat}
    (hgt : TabsOK gt) (hc : chainCheck gt (mkChain gt spec) = true)
    (hq : tabOK q.1 q.2 = true) (hm : chainMemberCheck gt spec q = true) :
    Perm.Gen (permsOf gt) (tpermP q) := by
  have ha : Agree (fun i => ap q.1 i) (tpermP q) := by
    intro i
    exact tperm_toFun hq i
  exact ((mkChain_spec spec gt hgt hc).1 _ _ ha).mp hm

@[expose] public def normalCheck (outer target : List (Nat × Nat))
    (targetSpec : List (Nat × List (List Nat))) : Bool :=
  outer.all (fun a => target.all (fun b =>
    chainMemberCheck target targetSpec (pairConjugate a b)
      && chainMemberCheck target targetSpec (pairConjugate (pairInv a) b)))

@[expose] public def mixedCommCheck (outer middle target : List (Nat × Nat))
    (targetSpec : List (Nat × List (List Nat))) : Bool :=
  outer.all (fun a => middle.all (fun b =>
    chainMemberCheck target targetSpec (pairCommutator a b)))

set_option maxHeartbeats 4000000 in
public theorem normalSeriesCert :
    normalCheck stabGt derivedOneGt derivedOneSpec = true
      ∧ normalCheck derivedOneGt derivedTwoGt derivedTwoSpec = true
      ∧ normalCheck derivedTwoGt derivedThreeGt derivedThreeSpec = true
      ∧ normalCheck stabGt derivedTwoGt derivedTwoSpec = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem commSeriesCert :
    mixedCommCheck stabGt stabGt derivedOneGt derivedOneSpec = true
      ∧ mixedCommCheck derivedOneGt derivedOneGt derivedTwoGt derivedTwoSpec = true
      ∧ mixedCommCheck derivedTwoGt derivedTwoGt derivedThreeGt derivedThreeSpec = true
      ∧ mixedCommCheck stabGt derivedOneGt derivedTwoGt derivedTwoSpec = true
      ∧ mixedCommCheck stabGt derivedTwoGt derivedTwoGt derivedTwoSpec = true := by
  decide +kernel

public theorem normal_of_check {outer target : List (Nat × Nat)}
    {spec : List (Nat × List (List Nat))}
    (houter : TabsOK outer) (htarget : TabsOK target)
    (hchain : chainCheck target (mkChain target spec) = true)
    (hsub : ∀ s, s ∈ permsOf target → Perm.Gen (permsOf outer) s)
    (hc : normalCheck outer target spec = true) :
    NormalIn (Perm.Gen (permsOf outer)) (Perm.Gen (permsOf target)) := by
  apply generated_normal_of_letters hsub
  intro s hs t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  have hrow := List.all_eq_true.mp hc a ha
  have hcell := List.all_eq_true.mp hrow b hb
  rw [Bool.and_eq_true] at hcell
  have haOK := houter a ha
  have hbOK := htarget b hb
  constructor
  · rw [← pairConjugate_perm (a := a) (b := b) haOK hbOK]
    exact chainMember_of_check htarget hchain
      (tabOK_mul haOK (tabOK_mul hbOK (tabOK_swap haOK))) hcell.1
  · rw [← pairInv_perm (a := a) haOK,
      ← pairConjugate_perm (a := pairInv a) (b := b) (tabOK_swap haOK) hbOK]
    exact chainMember_of_check htarget hchain
      (tabOK_mul (tabOK_swap haOK) (tabOK_mul hbOK haOK)) hcell.2

public theorem mixed_comm_of_check {outer middle target : List (Nat × Nat)}
    {spec : List (Nat × List (List Nat))}
    (houter : TabsOK outer) (hmiddle : TabsOK middle) (htarget : TabsOK target)
    (hchain : chainCheck target (mkChain target spec) = true)
    (hmiddleSub : ∀ s, s ∈ permsOf middle → Perm.Gen (permsOf outer) s)
    (hnormal : NormalIn (Perm.Gen (permsOf outer)) (Perm.Gen (permsOf target)))
    (hc : mixedCommCheck outer middle target spec = true) :
    ∀ g h, Perm.Gen (permsOf outer) g → Perm.Gen (permsOf middle) h →
      Perm.Gen (permsOf target) (commutator g h) := by
  apply generated_mixed_commutators_of_letters hmiddleSub hnormal
  intro s hs t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  have hm := List.all_eq_true.mp (List.all_eq_true.mp hc a ha) b hb
  have haOK := houter a ha
  have hbOK := hmiddle b hb
  rw [← pairCommutator_perm (a := a) (b := b) haOK hbOK]
  exact chainMember_of_check htarget hchain
    (tabOK_mul haOK (tabOK_mul hbOK
      (tabOK_mul (tabOK_swap haOK) (tabOK_swap hbOK)))) hm

public theorem derivedOne_sub {s : Perm 120} (hs : s ∈ permsOf derivedOneGt) :
    Perm.Gen (permsOf stabGt) s :=
  gen_nextGt stabGt_ok hs

public theorem derivedTwo_sub_one {s : Perm 120} (hs : s ∈ permsOf derivedTwoGt) :
    Perm.Gen (permsOf derivedOneGt) s :=
  gen_nextGt derivedOneGt_ok hs

public theorem derivedThree_sub_two {s : Perm 120} (hs : s ∈ permsOf derivedThreeGt) :
    Perm.Gen (permsOf derivedTwoGt) s :=
  gen_nextGt derivedTwoGt_ok hs

public theorem derivedTwo_sub {s : Perm 120} (hs : s ∈ permsOf derivedTwoGt) :
    Perm.Gen (permsOf stabGt) s :=
  gen_sub (fun _ hq => derivedOne_sub hq) (derivedTwo_sub_one hs)

public theorem normalDerivedOne :
    NormalIn (Perm.Gen (permsOf stabGt)) (Perm.Gen (permsOf derivedOneGt)) :=
  normal_of_check stabGt_ok derivedOneGt_ok derivedOneChain
    (fun s => derivedOne_sub (s := s))
    normalSeriesCert.1

public theorem normalDerivedTwoInOne :
    NormalIn (Perm.Gen (permsOf derivedOneGt)) (Perm.Gen (permsOf derivedTwoGt)) :=
  normal_of_check derivedOneGt_ok derivedTwoGt_ok derivedTwoChain
    (fun s => derivedTwo_sub_one (s := s))
    normalSeriesCert.2.1

public theorem normalDerivedThreeInTwo :
    NormalIn (Perm.Gen (permsOf derivedTwoGt)) (Perm.Gen (permsOf derivedThreeGt)) :=
  normal_of_check derivedTwoGt_ok derivedThreeGt_ok derivedThreeChain
    (fun s => derivedThree_sub_two (s := s))
    normalSeriesCert.2.2.1

public theorem normalDerivedTwo :
    NormalIn (Perm.Gen (permsOf stabGt)) (Perm.Gen (permsOf derivedTwoGt)) :=
  normal_of_check stabGt_ok derivedTwoGt_ok derivedTwoChain
    (fun s => derivedTwo_sub (s := s))
    normalSeriesCert.2.2.2

public theorem commOneAll : ∀ g h,
    Perm.Gen (permsOf stabGt) g → Perm.Gen (permsOf stabGt) h →
      Perm.Gen (permsOf derivedOneGt) (commutator g h) :=
  mixed_comm_of_check stabGt_ok stabGt_ok derivedOneGt_ok derivedOneChain
    (fun _ hs => Perm.Gen.mem_gen hs) normalDerivedOne commSeriesCert.1

public theorem commTwoAll : ∀ g h,
    Perm.Gen (permsOf derivedOneGt) g → Perm.Gen (permsOf derivedOneGt) h →
      Perm.Gen (permsOf derivedTwoGt) (commutator g h) :=
  mixed_comm_of_check derivedOneGt_ok derivedOneGt_ok derivedTwoGt_ok derivedTwoChain
    (fun _ hs => Perm.Gen.mem_gen hs) normalDerivedTwoInOne commSeriesCert.2.1

public theorem commThreeAll : ∀ g h,
    Perm.Gen (permsOf derivedTwoGt) g → Perm.Gen (permsOf derivedTwoGt) h →
      Perm.Gen (permsOf derivedThreeGt) (commutator g h) :=
  mixed_comm_of_check derivedTwoGt_ok derivedTwoGt_ok derivedThreeGt_ok derivedThreeChain
    (fun _ hs => Perm.Gen.mem_gen hs) normalDerivedThreeInTwo commSeriesCert.2.2.1

public theorem lowerTwoAll : ∀ g h,
    Perm.Gen (permsOf stabGt) g → Perm.Gen (permsOf derivedOneGt) h →
      Perm.Gen (permsOf derivedTwoGt) (commutator g h) :=
  mixed_comm_of_check stabGt_ok derivedOneGt_ok derivedTwoGt_ok derivedTwoChain
    (fun s => derivedOne_sub (s := s)) normalDerivedTwo commSeriesCert.2.2.2.1

public theorem lowerThreeAll : ∀ g h,
    Perm.Gen (permsOf stabGt) g → Perm.Gen (permsOf derivedTwoGt) h →
      Perm.Gen (permsOf derivedTwoGt) (commutator g h) :=
  mixed_comm_of_check stabGt_ok derivedTwoGt_ok derivedTwoGt_ok derivedTwoChain
    (fun s => derivedTwo_sub (s := s)) normalDerivedTwo commSeriesCert.2.2.2.2

set_option maxHeartbeats 4000000 in
public theorem derivedOneGeneratorsComm : ∀ s, s ∈ permsOf derivedOneGt →
    ∃ a ∈ permsOf stabGt, ∃ b ∈ permsOf stabGt, s = commutator a b := by
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem derivedTwoGeneratorsComm : ∀ s, s ∈ permsOf derivedTwoGt →
    ∃ a ∈ permsOf derivedOneGt, ∃ b ∈ permsOf derivedOneGt,
      s = commutator a b := by
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem derivedThreeGeneratorsComm : ∀ s, s ∈ permsOf derivedThreeGt →
    ∃ a ∈ permsOf derivedTwoGt, ∃ b ∈ permsOf derivedTwoGt,
      s = commutator a b := by
  decide +kernel

public theorem derivedOneExact :
    DerivedOf (Perm.Gen (permsOf stabGt)) (Perm.Gen (permsOf derivedOneGt)) := by
  apply exact_commClosure_of_generators commOneAll
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := derivedOneGeneratorsComm s hs
  exact CommClosure.comm (Perm.Gen.mem_gen ha) (Perm.Gen.mem_gen hb)

public theorem derivedTwoExact :
    DerivedOf (Perm.Gen (permsOf derivedOneGt))
      (Perm.Gen (permsOf derivedTwoGt)) := by
  apply exact_commClosure_of_generators commTwoAll
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := derivedTwoGeneratorsComm s hs
  exact CommClosure.comm (Perm.Gen.mem_gen ha) (Perm.Gen.mem_gen hb)

public theorem derivedThreeExact :
    DerivedOf (Perm.Gen (permsOf derivedTwoGt))
      (Perm.Gen (permsOf derivedThreeGt)) := by
  apply exact_commClosure_of_generators commThreeAll
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := derivedThreeGeneratorsComm s hs
  exact CommClosure.comm (Perm.Gen.mem_gen ha) (Perm.Gen.mem_gen hb)

set_option maxHeartbeats 4000000 in
public theorem derivedThreeGeneratorsAbelian : ∀ a, a ∈ permsOf derivedThreeGt →
    ∀ b, b ∈ permsOf derivedThreeGt →
      commutator a b = Perm.one 120 := by
  decide +kernel

public theorem trivial_normal (G : Perm 120 → Prop) :
    NormalIn G (Perm.Gen ([] : List (Perm 120))) := by
  intro g h _ hh
  have he := (gen_nil_iff h).mp hh
  rw [he, conjugate_one]
  exact Perm.Gen.one

public theorem derivedFourAll : ∀ g h,
    Perm.Gen (permsOf derivedThreeGt) g → Perm.Gen (permsOf derivedThreeGt) h →
      Perm.Gen ([] : List (Perm 120)) (commutator g h) := by
  apply generated_mixed_commutators_of_letters
    (fun s hs => Perm.Gen.mem_gen hs) (trivial_normal _)
  intro a ha b hb
  apply (gen_nil_iff _).mpr
  exact derivedThreeGeneratorsAbelian a ha b hb

public theorem derivedFourExact :
    DerivedOf (Perm.Gen (permsOf derivedThreeGt))
      (Perm.Gen ([] : List (Perm 120))) := by
  apply exact_commClosure_of_generators derivedFourAll
  intro s hs
  exact absurd hs (by simp)

/-! ### The non-terminating lower-central term -/

@[expose] public def mixedCommutatorGt (outer middle : List (Nat × Nat)) :
    List (Nat × Nat) :=
  (List.range outer.length).flatMap (fun i =>
    (List.range middle.length).map (fun j =>
      pairCommutator (outer.getD i (idT, idT)) (middle.getD j (idT, idT))))

@[expose] public def lowerTwoGt : List (Nat × Nat) :=
  mixedCommutatorGt stabGt derivedOneGt

@[expose] public def lowerThreeGt : List (Nat × Nat) :=
  mixedCommutatorGt stabGt derivedTwoGt

@[expose] public def lowerTwoWitnessWords : List (List Nat) :=
  [[16], [16, 15, 10, 14], [10, 3], [3, 26]]

@[expose] public def lowerThreeWitnessWords : List (List Nat) :=
  [[10, 0], [24, 18], [4], [5, 14]]

public theorem getD_tabOK {gt : List (Nat × Nat)} (hgt : TabsOK gt) (i : Nat) :
    tabOK (gt.getD i (idT, idT)).1 (gt.getD i (idT, idT)).2 = true := by
  rcases getD_mem_or (idT, idT) gt i with h | h
  · rw [h]; exact tabOK_idT
  · exact hgt _ h

public theorem mixedCommutatorGt_ok {outer middle : List (Nat × Nat)}
    (ho : TabsOK outer) (hm : TabsOK middle) :
    TabsOK (mixedCommutatorGt outer middle) := by
  intro q hq
  obtain ⟨i, hi, hqi⟩ := List.mem_flatMap.mp hq
  obtain ⟨j, hj, hqj⟩ := List.mem_map.mp hqi
  subst q
  exact tabOK_mul (getD_tabOK ho i)
    (tabOK_mul (getD_tabOK hm j)
      (tabOK_mul (tabOK_swap (getD_tabOK ho i))
        (tabOK_swap (getD_tabOK hm j))))

public theorem mixedGeneratorClosure {outer middle : List (Nat × Nat)}
    (ho : TabsOK outer) (hm : TabsOK middle) {s : Perm 120}
    (hs : s ∈ permsOf (mixedCommutatorGt outer middle)) :
    CommClosure (Perm.Gen (permsOf outer)) (Perm.Gen (permsOf middle)) s := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
  obtain ⟨i, hi, hqi⟩ := List.mem_flatMap.mp hq
  obtain ⟨j, hj, hqj⟩ := List.mem_map.mp hqi
  subst q
  rw [pairCommutator_perm (getD_tabOK ho i) (getD_tabOK hm j)]
  apply CommClosure.comm
  · apply Perm.Gen.mem_gen
    rw [permsOf, List.mem_map]
    have hilt : i < outer.length := List.mem_range.mp hi
    have hmem : outer.getD i (idT, idT) ∈ outer := by
      rw [← List.getElem_eq_getD (l := outer) (i := i) (h := hilt) (idT, idT)]
      exact List.getElem_mem _
    exact ⟨outer.getD i (idT, idT), hmem, rfl⟩
  · apply Perm.Gen.mem_gen
    rw [permsOf, List.mem_map]
    have hjlt : j < middle.length := List.mem_range.mp hj
    have hmem : middle.getD j (idT, idT) ∈ middle := by
      rw [← List.getElem_eq_getD (l := middle) (i := j) (h := hjlt) (idT, idT)]
      exact List.getElem_mem _
    exact ⟨middle.getD j (idT, idT), hmem, rfl⟩

public theorem commClosure_of_gen {G H : Perm 120 → Prop} {gt : List (Perm 120)}
    (hgt : ∀ s, s ∈ gt → CommClosure G H s) {g : Perm 120}
    (hg : Perm.Gen gt g) : CommClosure G H g := by
  induction hg with
  | one => exact CommClosure.one
  | step _ hs ih => exact CommClosure.comp ih (hgt _ hs)
  | stepInv _ hs ih => exact CommClosure.comp ih (CommClosure.inv (hgt _ hs))

set_option maxHeartbeats 4000000 in
public theorem lowerTwoWitnesses : ∀ s, s ∈ permsOf derivedTwoGt →
    ∃ w ∈ lowerTwoWitnessWords,
      s = evalP (permsOf lowerTwoGt) w := by
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem lowerThreeWitnesses : ∀ s, s ∈ permsOf derivedTwoGt →
    ∃ w ∈ lowerThreeWitnessWords,
      s = evalP (permsOf lowerThreeGt) w := by
  decide +kernel

public theorem lowerTwoExact :
    LowerCentralStep (Perm.Gen (permsOf stabGt))
      (Perm.Gen (permsOf derivedOneGt)) (Perm.Gen (permsOf derivedTwoGt)) := by
  apply exact_commClosure_of_generators lowerTwoAll
  intro s hs
  obtain ⟨w, _, he⟩ := lowerTwoWitnesses s hs
  rw [he]
  apply commClosure_of_gen
    (G := Perm.Gen (permsOf stabGt)) (H := Perm.Gen (permsOf derivedOneGt))
  · intro t ht
    exact mixedGeneratorClosure stabGt_ok derivedOneGt_ok ht
  · exact gen_evalP _ w

public theorem lowerThreeExact :
    LowerCentralStep (Perm.Gen (permsOf stabGt))
      (Perm.Gen (permsOf derivedTwoGt)) (Perm.Gen (permsOf derivedTwoGt)) := by
  apply exact_commClosure_of_generators lowerThreeAll
  intro s hs
  obtain ⟨w, _, he⟩ := lowerThreeWitnesses s hs
  rw [he]
  apply commClosure_of_gen
    (G := Perm.Gen (permsOf stabGt)) (H := Perm.Gen (permsOf derivedTwoGt))
  · intro t ht
    exact mixedGeneratorClosure stabGt_ok derivedTwoGt_ok ht
  · exact gen_evalP _ w

/-! ## The center -/

@[expose] public def GaugeCenter (g : Perm 120) : Prop :=
  D28 W0 g ∧ ∀ h : Perm 120, D28 W0 h → g.comp h = h.comp g

@[expose] public def GeneratedCenter (g : Perm 120) : Prop :=
  Perm.Gen (permsOf stabGt) g ∧ ∀ h : Perm 120,
    Perm.Gen (permsOf stabGt) h → g.comp h = h.comp g

public theorem generatedCenter_iff (g : Perm 120) : GeneratedCenter g ↔ GaugeCenter g := by
  constructor
  · rintro ⟨hg, hc⟩
    exact ⟨(gauge_eq g).mpr hg, fun h hh => hc h ((gauge_eq h).mp hh)⟩
  · rintro ⟨hg, hc⟩
    exact ⟨(gauge_eq g).mp hg, fun h hh => hc h ((gauge_eq h).mpr hh)⟩

public theorem commute_inverse_right {a b : Perm 120} (h : a.comp b = b.comp a) :
    a.comp b.inv = b.inv.comp a := by
  apply Perm.ext
  intro i
  apply b.toFun_injective
  have he := congrArg (fun p : Perm 120 => p.toFun (b.invFun i)) h
  simpa only [Perm.comp_apply, Perm.inv_apply, Perm.left_inv, Perm.right_inv] using he.symm

public theorem generatedCenter_subgroup : SubgroupPred GeneratedCenter := by
  refine ⟨⟨Perm.Gen.one, fun h _ => by rw [Perm.one_comp, Perm.comp_one]⟩, ?_, ?_⟩
  · rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨Perm.Gen.comp_mem ha hb, fun h hh => ?_⟩
    rw [Perm.comp_assoc, hcb h hh, ← Perm.comp_assoc, hca h hh, Perm.comp_assoc]
  · rintro a ⟨ha, hca⟩
    refine ⟨Perm.Gen.inv_mem ha, fun h hh => ?_⟩
    exact (commute_inverse_right (hca h hh).symm).symm

public theorem commutes_with_generated {z : Perm 120}
    (hz : ∀ s, s ∈ permsOf stabGt → z.comp s = s.comp z) :
    ∀ g, Perm.Gen (permsOf stabGt) g → z.comp g = g.comp z := by
  intro g hg
  induction hg with
  | one => rw [Perm.comp_one, Perm.one_comp]
  | @step p s hp hs ih =>
    rw [← Perm.comp_assoc, ih, Perm.comp_assoc, hz s hs]
    exact (Perm.comp_assoc p s z).symm
  | @stepInv p s hp hs ih =>
    rw [← Perm.comp_assoc, ih, Perm.comp_assoc, commute_inverse_right (hz s hs)]
    exact (Perm.comp_assoc p s.inv z).symm

@[expose] public def centerWord : List Nat :=
  [0, 2, 4, 6, 4, 0, 4, 0, 2, 4, 6, 4, 0, 4]

@[expose] public def centerQ : Nat × Nat := evalT stabGt centerWord

@[expose] public def centerElement : Perm 120 := tpermP centerQ

set_option maxHeartbeats 4000000 in
public theorem centerElementCert :
    stabGt.all (fun q => decide
      (centerElement.comp (tpermP q) = (tpermP q).comp centerElement)) = true
      ∧ centerElement.comp centerElement = Perm.one 120
      ∧ centerElement ≠ Perm.one 120
      ∧ centerElement.toFun (fin120 0) = fin120 44
      ∧ centerElement.invFun (fin120 44) = fin120 0 := by
  decide +kernel

public theorem centerElement_gen : Perm.Gen (permsOf stabGt) centerElement := by
  rw [centerElement, centerQ, ← evalP_permsOf stabGt_ok]
  exact gen_evalP _ centerWord

public theorem centerElement_center : GeneratedCenter centerElement := by
  refine ⟨centerElement_gen, commutes_with_generated (fun s hs => ?_)⟩
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
  exact of_decide_eq_true (List.all_eq_true.mp centerElementCert.1 q hq)

@[expose] public def centerPointWords : List (List Nat) :=
  [[0], [3, 0, 2], [5, 1, 2, 0, 4], [5, 1, 4, 0, 4], [7, 5, 0, 4, 6]]

@[expose] public def centerPointGt : List (Nat × Nat) :=
  centerPointWords.map (evalT stabGt)

@[expose] public def centerPointOK : Bool :=
  centerPointGt.all (fun q => Nat.beq (ap q.1 0) 0)
    && allLt (fun y => Bool.not (Bitset.mem W0 y)
      || Bool.not (centerPointGt.all (fun q => Nat.beq (ap q.1 y) y))
      || decide (y = 0 ∨ y = 44)) 120

set_option maxHeartbeats 4000000 in
public theorem centerPointCert : centerPointOK = true := by decide +kernel

public theorem centerPointGt_ok : TabsOK centerPointGt :=
  tabsOK_nextGt stabGt_ok centerPointWords

public theorem center_image_candidates {g : Perm 120} (hg : GeneratedCenter g) :
    (g.toFun (fin120 0)).val = 0 ∨ (g.toFun (fin120 0)).val = 44 := by
  have hW : D28 W0 g := (gauge_eq g).mpr hg.1
  have hzero : (0 : Nat) ∈ W0 := by decide +kernel
  have hyW : (g.toFun (fin120 0)).val ∈ W0 :=
    (mem_actP_iff hW.2 (fin120 0)).mpr hzero
  have hcert := centerPointCert
  rw [centerPointOK, Bool.and_eq_true] at hcert
  have hfix : centerPointGt.all
      (fun q => Nat.beq (ap q.1 (g.toFun (fin120 0)).val)
        (g.toFun (fin120 0)).val) = true := by
    apply List.all_eq_true.mpr
    intro q hq
    have hq0 := List.all_eq_true.mp hcert.1 q hq
    have hqGen : Perm.Gen (permsOf stabGt) (tpermP q) :=
      gen_nextGt stabGt_ok (by
        show tpermP q ∈ permsOf centerPointGt
        rw [permsOf, List.mem_map]
        exact ⟨q, hq, rfl⟩)
    have hc := congrArg (fun p : Perm 120 => (p.toFun (fin120 0)).val)
      (hg.2 (tpermP q) hqGen)
    have hqOK := centerPointGt_ok q hq
    simp only [Perm.comp_apply] at hc
    change (g.toFun ((tperm q.1 q.2).toFun (fin120 0))).val =
      ((tperm q.1 q.2).toFun (g.toFun (fin120 0))).val at hc
    have hp0 : (tperm q.1 q.2).toFun (fin120 0) = fin120 0 := by
      apply Fin.eq_of_val_eq
      rw [tperm_toFun hqOK, fin120_val (by decide),
        Nat.eq_of_beq_eq_true hq0]
    rw [hp0, tperm_toFun hqOK] at hc
    rw [hc.symm]
    exact Nat.beq_refl _
  have hcell := allLt_true _ _ hcert.2
    (g.toFun (fin120 0)).val (g.toFun (fin120 0)).isLt
  have hyWb : Bitset.mem W0 (g.toFun (fin120 0)).val = true := hyW
  simp only [hyWb, hfix, Bool.not_true, Bool.false_or] at hcell
  exact of_decide_eq_true hcell

@[expose] public def centerReachWord (b : Nat) : List Nat :=
  if b = 0 then [] else if b = 1 then [2] else if b = 2 then [4]
  else if b = 4 then [6, 0, 2, 6, 4, 6, 4, 0, 6, 4, 6, 4, 0, 4, 6, 4, 6, 4, 6]
  else [6, 4, 6, 4, 0, 4, 6, 4, 6, 4, 6]

@[expose] public def centerReachBases : List Nat := [0, 1, 2, 4, 6]

set_option maxHeartbeats 4000000 in
public theorem centerReachCert : centerReachBases.all (fun b =>
    Nat.beq (ap (evalT stabGt (centerReachWord b)).1 0) b) = true := by
  decide +kernel

public theorem central_fixes_reached {g : Perm 120} (hg : GeneratedCenter g)
    (h0 : (g.toFun (fin120 0)).val = 0) {b : Nat} (hb : b ∈ centerReachBases) :
    (g.toFun (fin120 b)).val = b := by
  let q := evalT stabGt (centerReachWord b)
  let p := tpermP q
  have hqOK : tabOK q.1 q.2 = true := tabOK_evalT stabGt_ok _
  have hpGen : Perm.Gen (permsOf stabGt) p := by
    show Perm.Gen (permsOf stabGt) (tpermP (evalT stabGt (centerReachWord b)))
    rw [← evalP_permsOf stabGt_ok]
    exact gen_evalP _ _
  have hp0v : (p.toFun (fin120 0)).val = b := by
    change ((tperm q.1 q.2).toFun (fin120 0)).val = b
    rw [tperm_toFun hqOK, fin120_val (by decide)]
    exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp centerReachCert b hb)
  have hblt : b < 120 := by
    simp only [centerReachBases, List.mem_cons, List.not_mem_nil, or_false] at hb
    omega
  have hp0 : p.toFun (fin120 0) = fin120 b :=
    Fin.eq_of_val_eq (by rw [hp0v, fin120_val hblt])
  have hg0 : g.toFun (fin120 0) = fin120 0 :=
    Fin.eq_of_val_eq (by rw [h0, fin120_val (by decide)])
  have hc := congrArg (fun r : Perm 120 => r.toFun (fin120 0)) (hg.2 p hpGen)
  simp only [Perm.comp_apply, hp0, hg0] at hc
  have hcv := congrArg Fin.val hc
  rwa [fin120_val hblt] at hcv

public theorem gauge_fix_bases_trivial {g : Perm 120}
    (hg : Perm.Gen (permsOf stabGt) g)
    (hfix : ∀ b, b ∈ centerReachBases → (g.toFun (fin120 b)).val = b) :
    g = Perm.one 120 := by
  let f : Nat → Nat := fun i => (g.toFun (fin120 i)).val
  have ha : Agree f g := by
    intro i
    show (g.toFun i).val = (g.toFun (fin120 i.val)).val
    rw [show fin120 i.val = i from Fin.eq_of_val_eq (fin120_val i.isLt)]
  have hm : memChain (mkChain stabGt stabSpec) f = true :=
    ((mkChain_spec stabSpec stabGt stabGt_ok stabChain).1 f g ha).mpr hg
  have hlt : ∀ i, i < 120 → f i < 120 := fun i _ => (g.toFun (fin120 i)).isLt
  have hbs : ∀ b, b ∈ stabSpec.map Prod.fst → f b = b := by
    intro b hb
    have hb' : b ∈ centerReachBases := by
      simpa [stabSpec, centerReachBases] using hb
    exact hfix b hb'
  have hlevels : ∀ l ∈ mkChain stabGt stabSpec, f l.bp = l.bp := by
    intro l hl
    obtain ⟨p, hp, hbp⟩ := mkChain_bp stabSpec stabGt l hl
    rw [hbp]
    exact hbs p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hall := memChain_fix stabSpec stabGt stabGt_ok stabChain f hlt hlevels hm
  apply Perm.ext
  intro i
  apply Fin.eq_of_val_eq
  have hi := hall i.val i.isLt
  show (g.toFun i).val = i.val
  change (g.toFun (fin120 i.val)).val = i.val at hi
  rw [show fin120 i.val = i from Fin.eq_of_val_eq (fin120_val i.isLt)] at hi
  exact hi

public theorem central_fix_zero {g : Perm 120} (hg : GeneratedCenter g)
    (h0 : (g.toFun (fin120 0)).val = 0) : g = Perm.one 120 := by
  apply gauge_fix_bases_trivial hg.1
  intro b hb
  exact central_fixes_reached hg h0 hb

public theorem center_exact {g : Perm 120} (hg : GeneratedCenter g) :
    g = Perm.one 120 ∨ g = centerElement := by
  rcases center_image_candidates hg with h0 | h44
  · exact Or.inl (central_fix_zero hg h0)
  · let q := centerElement.inv.comp g
    have hq : GeneratedCenter q :=
      generatedCenter_subgroup.2.1 centerElement.inv g
        (generatedCenter_subgroup.2.2 centerElement centerElement_center) hg
    have hg0 : g.toFun (fin120 0) = fin120 44 :=
      Fin.eq_of_val_eq (by rw [h44, fin120_val (by decide)])
    have hq0 : (q.toFun (fin120 0)).val = 0 := by
      show (centerElement.invFun (g.toFun (fin120 0))).val = 0
      rw [hg0, centerElementCert.2.2.2.2]
      rfl
    have hone := central_fix_zero hq hq0
    right
    calc
      g = (centerElement.comp centerElement.inv).comp g := by
        rw [Perm.comp_inv, Perm.one_comp]
      _ = centerElement.comp q := rfl
      _ = centerElement := by rw [hone, Perm.comp_one]

@[expose] public def gaugeCenterList : List (Perm 120) :=
  [Perm.one 120, centerElement]

public theorem gaugeCenterList_nodup : gaugeCenterList.Nodup := by
  rw [gaugeCenterList]
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
  simpa using centerElementCert.2.2.1.symm

public theorem gaugeCenterOrder : HasOrderP GaugeCenter 2 := by
  refine ⟨gaugeCenterList, gaugeCenterList_nodup, fun g => ?_, rfl⟩
  constructor
  · intro hm
    apply (generatedCenter_iff g).mp
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨Perm.Gen.one, fun h _ => by rw [Perm.one_comp, Perm.comp_one]⟩
    · exact List.mem_singleton.mp hm ▸ centerElement_center
  · intro hc
    rcases center_exact ((generatedCenter_iff g).mpr hc) with rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)

/-! ## The eight cosets of the derived subgroup -/

@[expose] public def abelianRepWords : List (List Nat) :=
  [[6, 4, 0], [4, 0], [6, 4], [6, 0], [6], [4], [0], []]

@[expose] public def abelianRepGt : List (Nat × Nat) :=
  abelianRepWords.map (evalT stabGt)

@[expose] public def abelianRepQ (i : Nat) : Nat × Nat :=
  abelianRepGt.getD i (idT, idT)

@[expose] public def abelianRepP (i : Nat) : Perm 120 :=
  tpermP (abelianRepQ i)

public theorem abelianRepGt_ok : TabsOK abelianRepGt :=
  tabsOK_nextGt stabGt_ok abelianRepWords

public theorem abelianRepQ_ok (i : Nat) :
    tabOK (abelianRepQ i).1 (abelianRepQ i).2 = true :=
  getD_tabOK abelianRepGt_ok i

@[expose] public def abelianJ : List (List Nat) :=
  [[2, 2, 2, 2, 3, 3, 1, 1], [5, 5, 5, 5, 6, 6, 0, 0],
   [0, 0, 0, 0, 4, 4, 5, 5], [4, 4, 4, 4, 0, 0, 6, 6],
   [3, 3, 3, 3, 2, 2, 7, 7], [1, 1, 1, 1, 7, 7, 2, 2],
   [7, 7, 7, 7, 1, 1, 3, 3], [6, 6, 6, 6, 5, 5, 4, 4]]

@[expose] public def abelianK : List (List (List Nat)) :=
  [[[], [], [6, 5, 6, 3], [6, 5, 6, 3], [6, 5, 6, 3, 4], [6, 5, 6, 3, 4],
      [6, 5, 2], [6, 5, 2]],
   [[], [], [3, 4], [3, 4], [3], [3], [3, 4, 6], [3, 4, 6]],
   [[], [], [6, 3, 4, 6], [6, 3, 4, 6], [], [], [6], [6]],
   [[], [], [5], [5], [5, 6, 3, 4, 6], [5, 6, 3, 4, 6], [5], [5]],
   [[], [], [4], [4], [], [], [], []],
   [[], [], [5, 2], [5, 2], [], [], [6], [6]],
   [[], [], [4], [4], [2], [2], [4], [4]],
   [[], [], [5], [5], [], [], [], []]]

@[expose] public def abelianJAt (i l : Nat) : Nat :=
  (abelianJ.getD i []).getD l 0

@[expose] public def abelianKAt (i l : Nat) : List Nat :=
  (abelianK.getD i []).getD l []

@[expose] public def abelianStepCheck (i l : Nat) : Bool :=
  decide (abelianJAt i l < 8)
    && Nat.beq
      (pairMul (abelianRepQ i) (genT stabGt l)).1
      (pairMul (evalT derivedOneGt (abelianKAt i l))
        (abelianRepQ (abelianJAt i l))).1

set_option maxHeartbeats 4000000 in
public theorem abelianStepCert :
    allLt (fun i => allLt (fun l => abelianStepCheck i l) 8) 8 = true := by
  decide +kernel

public theorem abelian_step {i l : Nat} (hi : i < 8) (hl : l < 8) :
    abelianJAt i l < 8 ∧
      (abelianRepP i).comp (tpermP (genT stabGt l)) =
        (tpermP (evalT derivedOneGt (abelianKAt i l))).comp
          (abelianRepP (abelianJAt i l)) := by
  have hc := allLt_true _ _ (allLt_true _ _ abelianStepCert i hi) l hl
  rw [abelianStepCheck, Bool.and_eq_true] at hc
  refine ⟨of_decide_eq_true hc.1, ?_⟩
  have ha := abelianRepQ_ok i
  have hb := tabOK_genT stabGt_ok l
  have hk := tabOK_evalT derivedOneGt_ok (abelianKAt i l)
  have hj := abelianRepQ_ok (abelianJAt i l)
  change (tpermP (abelianRepQ i)).comp (tpermP (genT stabGt l)) =
    (tpermP (evalT derivedOneGt (abelianKAt i l))).comp
      (tpermP (abelianRepQ (abelianJAt i l)))
  rw [← pairMul_perm (a := abelianRepQ i) (b := genT stabGt l) ha hb,
    ← pairMul_perm (a := evalT derivedOneGt (abelianKAt i l))
      (b := abelianRepQ (abelianJAt i l)) hk hj]
  exact tperm_congr (tabOK_mul ha hb) (tabOK_mul hk hj)
    (Nat.eq_of_beq_eq_true hc.2)

public theorem abelianRepSeven : abelianRepP 7 = Perm.one 120 := by
  decide +kernel

public theorem abelian_coset {g : Perm 120} (hg : Perm.Gen (permsOf stabGt) g) :
    ∃ i : Nat, i < 8 ∧ ∃ k : Perm 120,
      Perm.Gen (permsOf derivedOneGt) k ∧ g = k.comp (abelianRepP i) := by
  induction hg with
  | one =>
    exact ⟨7, by decide, Perm.one 120, Perm.Gen.one, by rw [abelianRepSeven,
      Perm.comp_one]⟩
  | @step p s hp hs ih =>
    obtain ⟨i, hi, k, hk, he⟩ := ih
    obtain ⟨l, hl, hsl, _⟩ := stab_letter hs
    obtain ⟨hj, hstep⟩ := abelian_step hi (by omega : l < 8)
    let k' := tpermP (evalT derivedOneGt (abelianKAt i l))
    refine ⟨abelianJAt i l, hj, k.comp k',
      Perm.Gen.comp_mem hk ?_, ?_⟩
    · show Perm.Gen (permsOf derivedOneGt)
        (tpermP (evalT derivedOneGt (abelianKAt i l)))
      rw [← evalP_permsOf derivedOneGt_ok]
      exact gen_evalP _ _
    · rw [he, hsl, Perm.comp_assoc, hstep, ← Perm.comp_assoc]
  | @stepInv p s hp hs ih =>
    obtain ⟨i, hi, k, hk, he⟩ := ih
    obtain ⟨l, hl, _, hsli⟩ := stab_letter hs
    obtain ⟨hj, hstep⟩ := abelian_step hi hl
    let k' := tpermP (evalT derivedOneGt (abelianKAt i (l + 1)))
    refine ⟨abelianJAt i (l + 1), hj, k.comp k',
      Perm.Gen.comp_mem hk ?_, ?_⟩
    · show Perm.Gen (permsOf derivedOneGt)
        (tpermP (evalT derivedOneGt (abelianKAt i (l + 1))))
      rw [← evalP_permsOf derivedOneGt_ok]
      exact gen_evalP _ _
    · rw [he, hsli, Perm.comp_assoc, hstep, ← Perm.comp_assoc]

@[expose] public def abelianDistinctCheck : Bool :=
  allLt (fun i => allLt (fun j =>
    Bool.not (chainMemberCheck derivedOneGt derivedOneSpec
      (pairMul (abelianRepQ i) (pairInv (abelianRepQ j))))
      || decide (i = j)) 8) 8

set_option maxHeartbeats 4000000 in
public theorem abelianDistinctCert : abelianDistinctCheck = true := by decide +kernel

public theorem abelian_cosets_distinct {i j : Nat} (hi : i < 8) (hj : j < 8)
    {k l : Perm 120} (hk : Perm.Gen (permsOf derivedOneGt) k)
    (hl : Perm.Gen (permsOf derivedOneGt) l)
    (he : k.comp (abelianRepP i) = l.comp (abelianRepP j)) : i = j := by
  let q := pairMul (abelianRepQ i) (pairInv (abelianRepQ j))
  have hqOK : tabOK q.1 q.2 = true :=
    tabOK_mul (abelianRepQ_ok i) (tabOK_swap (abelianRepQ_ok j))
  have hperm : tpermP q = k.inv.comp l := by
    calc
      tpermP q = (tpermP (abelianRepQ i)).comp
          (tpermP (pairInv (abelianRepQ j))) :=
        pairMul_perm (a := abelianRepQ i) (b := pairInv (abelianRepQ j))
          (abelianRepQ_ok i) (tabOK_swap (abelianRepQ_ok j))
      _ = (abelianRepP i).comp (abelianRepP j).inv := by
        rw [pairInv_perm (a := abelianRepQ j) (abelianRepQ_ok j)]
        rfl
      _ =
          ((k.inv.comp k).comp (abelianRepP i)).comp (abelianRepP j).inv := by
        rw [Perm.inv_comp, Perm.one_comp]
      _ = k.inv.comp ((k.comp (abelianRepP i)).comp (abelianRepP j).inv) := rfl
      _ = k.inv.comp ((l.comp (abelianRepP j)).comp (abelianRepP j).inv) := by
        rw [he]
      _ = k.inv.comp l := by rw [Perm.comp_assoc, Perm.comp_inv, Perm.comp_one]
  have hqGen : Perm.Gen (permsOf derivedOneGt) (tpermP q) := by
    rw [hperm]
    exact Perm.Gen.comp_mem (Perm.Gen.inv_mem hk) hl
  have ha : Agree (fun x => ap q.1 x) (tpermP q) := by
    intro x
    exact tperm_toFun hqOK x
  have hm : chainMemberCheck derivedOneGt derivedOneSpec q = true :=
    ((mkChain_spec derivedOneSpec derivedOneGt derivedOneGt_ok derivedOneChain).1
      _ _ ha).mpr hqGen
  have hc := allLt_true _ _ (allLt_true _ _ abelianDistinctCert i hi) j hj
  rw [hm] at hc
  exact of_decide_eq_true hc

@[expose] public def abelianRepList : List (Perm 120) :=
  (List.range 8).map abelianRepP

public theorem abelianRepList_nodup : abelianRepList.Nodup := by
  apply nodup_map_inj abelianRepP (List.range 8) List.nodup_range
  intro i hi j hj he
  exact abelian_cosets_distinct (List.mem_range.mp hi) (List.mem_range.mp hj)
    Perm.Gen.one Perm.Gen.one (by rw [Perm.one_comp, Perm.one_comp, he])

public theorem abelianRepList_length : abelianRepList.length = 8 := by
  simp [abelianRepList]

@[expose] public def HasIndexEight (G H : Perm 120 → Prop) : Prop :=
  ∃ R : List (Perm 120), R.Nodup ∧ R.length = 8
    ∧ (∀ g, G g → ∃ k r, H k ∧ r ∈ R ∧ g = k.comp r)
    ∧ (∀ k l r s, H k → H l → r ∈ R → s ∈ R →
      k.comp r = l.comp s → r = s)

public theorem derivedIndexEight :
    HasIndexEight (Perm.Gen (permsOf stabGt)) (Perm.Gen (permsOf derivedOneGt)) := by
  refine ⟨abelianRepList, abelianRepList_nodup, abelianRepList_length, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, hi, k, hk, he⟩ := abelian_coset hg
    exact ⟨k, abelianRepP i, hk,
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, he⟩
  · intro k l r s hk hl hr hs he
    obtain ⟨i, hi, hir⟩ := List.mem_map.mp hr
    obtain ⟨j, hj, hjs⟩ := List.mem_map.mp hs
    subst r
    subst s
    have hij := abelian_cosets_distinct (List.mem_range.mp hi) (List.mem_range.mp hj)
      hk hl he
    rw [hij]

/-! ## Solvability and non-nilpotence -/

@[expose] public def LowerCentral (G : Perm 120 → Prop) : Nat → Perm 120 → Prop
  | 0 => G
  | n + 1 => CommClosure G (LowerCentral G n)

@[expose] public def NilpotentPred (G : Perm 120 → Prop) : Prop :=
  ∃ n : Nat, ∀ g : Perm 120, LowerCentral G n g → g = Perm.one 120

@[expose] public def SolvablePred (G : Perm 120 → Prop) : Prop :=
  ∃ D1 D2 D3 : Perm 120 → Prop,
    DerivedOf G D1 ∧ DerivedOf D1 D2 ∧ DerivedOf D2 D3
      ∧ DerivedOf D3 (Perm.Gen ([] : List (Perm 120)))

public theorem commClosure_mono_right {G H K : Perm 120 → Prop}
    (hsub : ∀ g, H g → K g) {g : Perm 120}
    (hg : CommClosure G H g) : CommClosure G K g := by
  induction hg with
  | one => exact CommClosure.one
  | comm hG hH => exact CommClosure.comm hG (hsub _ hH)
  | comp _ _ ih ih' => exact CommClosure.comp ih ih'
  | inv _ ih => exact CommClosure.inv ih

public theorem derivedTwo_in_every_lower : ∀ n : Nat, ∀ g : Perm 120,
    Perm.Gen (permsOf derivedTwoGt) g →
      LowerCentral (Perm.Gen (permsOf stabGt)) n g := by
  intro n
  induction n with
  | zero =>
    intro g hg
    exact gen_sub (fun s hs => derivedTwo_sub hs) hg
  | succ n ih =>
    intro g hg
    show CommClosure (Perm.Gen (permsOf stabGt))
      (LowerCentral (Perm.Gen (permsOf stabGt)) n) g
    apply commClosure_mono_right (fun h hh => ih h hh)
    exact (lowerThreeExact g).mp hg

@[expose] public def lowerWitness : Perm 120 :=
  tpermP (evalT derivedOneGt [0, 2, 1, 3])

public theorem lowerWitness_mem : Perm.Gen (permsOf derivedTwoGt) lowerWitness := by
  apply Perm.Gen.mem_gen
  show tpermP (evalT derivedOneGt [0, 2, 1, 3]) ∈ permsOf derivedTwoGt
  rw [permsOf, List.mem_map]
  exact ⟨evalT derivedOneGt [0, 2, 1, 3], by
    simp [derivedTwoGt, derivedTwoWords], rfl⟩

set_option maxHeartbeats 4000000 in
public theorem lowerWitness_ne : lowerWitness ≠ Perm.one 120 := by decide +kernel

public theorem gauge_not_nilpotent :
    ¬ NilpotentPred (Perm.Gen (permsOf stabGt)) := by
  rintro ⟨n, hn⟩
  exact lowerWitness_ne (hn lowerWitness
    (derivedTwo_in_every_lower n lowerWitness lowerWitness_mem))

public theorem gauge_solvable : SolvablePred (Perm.Gen (permsOf stabGt)) :=
  ⟨Perm.Gen (permsOf derivedOneGt), Perm.Gen (permsOf derivedTwoGt),
    Perm.Gen (permsOf derivedThreeGt), derivedOneExact, derivedTwoExact,
    derivedThreeExact, derivedFourExact⟩

public theorem gaugeOrderW0 : HasOrderP (D28 W0) 4608 := by
  rw [← W0_eq]
  exact gaugeOrderWitness

/-- `T55`.  The gauge group is solvable but not nilpotent.  Its center has
order two; its exact commutator subgroup has order `576` and index `8`; and its
derived series has orders `4608, 576, 144, 16, 1`.  The lower-central series is
nonterminating because its `144`-element term is equal to its own next term. -/
public theorem T55 :
    HasOrderP (D28 W0) 4608
      ∧ HasOrderP GaugeCenter 2
      ∧ SolvablePred (Perm.Gen (permsOf stabGt))
      ∧ ¬ NilpotentPred (Perm.Gen (permsOf stabGt))
      ∧ DerivedOf (Perm.Gen (permsOf stabGt))
          (Perm.Gen (permsOf derivedOneGt))
      ∧ HasOrder (permsOf derivedOneGt) 576
      ∧ HasIndexEight (Perm.Gen (permsOf stabGt))
          (Perm.Gen (permsOf derivedOneGt))
      ∧ DerivedOf (Perm.Gen (permsOf derivedOneGt))
          (Perm.Gen (permsOf derivedTwoGt))
      ∧ HasOrder (permsOf derivedTwoGt) 144
      ∧ DerivedOf (Perm.Gen (permsOf derivedTwoGt))
          (Perm.Gen (permsOf derivedThreeGt))
      ∧ HasOrder (permsOf derivedThreeGt) 16
      ∧ DerivedOf (Perm.Gen (permsOf derivedThreeGt))
          (Perm.Gen ([] : List (Perm 120)))
      ∧ HasOrder ([] : List (Perm 120)) 1
      ∧ LowerCentralStep (Perm.Gen (permsOf stabGt))
          (Perm.Gen (permsOf derivedOneGt)) (Perm.Gen (permsOf derivedTwoGt))
      ∧ LowerCentralStep (Perm.Gen (permsOf stabGt))
          (Perm.Gen (permsOf derivedTwoGt)) (Perm.Gen (permsOf derivedTwoGt)) :=
  ⟨gaugeOrderW0, gaugeCenterOrder, gauge_solvable, gauge_not_nilpotent,
    derivedOneExact, derivedOneOrder, derivedIndexEight, derivedTwoExact,
    derivedTwoOrder, derivedThreeExact, derivedThreeOrder, derivedFourExact,
    hasOrder_nil, lowerTwoExact, lowerThreeExact⟩

public theorem witness_kernel_normal {g k : Perm 120} (hg : D28 W0 g)
    (hk : stabPres Blocks.blkSet k) :
    stabPres Blocks.blkSet (conjugate g k) := by
  obtain ⟨t, ht⟩ := gauge_blocks hg
  refine ⟨Perm.Gen.comp_mem hg.1
      (Perm.Gen.comp_mem hk.1 (Perm.Gen.inv_mem hg.1)), fun a => ?_⟩
  have hinv : actP g.inv (Blocks.blkSet a) = Blocks.blkSet (t.invFun a) := by
    have h := congrArg (actP g.inv) (ht (t.invFun a))
    rw [t.right_inv] at h
    have hcancel : actP g.inv (actP g (Blocks.blkSet (t.invFun a))) =
        Blocks.blkSet (t.invFun a) := actP_inv g (Blocks.blkIsBlock _).1
    rw [hcancel] at h
    exact h.symm
  simp only [conjugate, actP_comp]
  rw [hinv, hk.2, ht, t.right_inv]

public theorem cosList_gauge {c : Perm 120} (hc : c ∈ cosList) : D28 W0 c := by
  obtain ⟨i, _, rfl⟩ := mem_cosList.mp hc
  exact cosP_gauge i

public theorem kernel_inter_cosList {c : Perm 120} (hc : c ∈ cosList)
    (hk : stabPres Blocks.blkSet c) : c = Perm.one 120 := by
  obtain ⟨i, hi, rfl⟩ := mem_cosList.mp hc
  rw [cos_fix_zero hi hk.2, cosP_zero]

public theorem witness_factorisation {g : Perm 120} (hg : D28 W0 g) :
    ∃ k c : Perm 120, stabPres Blocks.blkSet k ∧ c ∈ cosList ∧ g = k.comp c := by
  obtain ⟨i, hi, k, hk, he⟩ := T31.2.2 g hg
  exact ⟨k, cosP i, (stabPres_eq k).mpr hk,
    mem_cosList.mpr ⟨i, hi, rfl⟩, he⟩

/-- `T54`.  The gauge extension splits over the dihedral complement. -/
public theorem T54 :
    HasOrderP (stabPres Blocks.blkSet) 576
      ∧ cosList.Nodup ∧ cosList.length = 8
      ∧ (∀ c, c ∈ cosList → D28 W0 c)
      ∧ (∀ c, c ∈ cosList → stabPres Blocks.blkSet c → c = Perm.one 120)
      ∧ (∀ g, D28 W0 g → ∃ k c, stabPres Blocks.blkSet k
        ∧ c ∈ cosList ∧ g = k.comp c) :=
  ⟨T39p, cosList_nodup, cosList_length,
    (fun c => cosList_gauge (c := c)),
    (fun c => kernel_inter_cosList (c := c)),
    (fun g => witness_factorisation (g := g))⟩

public theorem witness_factorisation_unique {g k c l d : Perm 120}
    (hk : stabPres Blocks.blkSet k) (hc : c ∈ cosList)
    (hl : stabPres Blocks.blkSet l) (hd : d ∈ cosList)
    (he : g = k.comp c) (he' : g = l.comp d) : k = l ∧ c = d := by
  obtain ⟨i, hi, rfl⟩ := mem_cosList.mp hc
  obtain ⟨j, hj, rfl⟩ := mem_cosList.mp hd
  have hp : D28a Blocks.blkSet (cosP i) = D28a Blocks.blkSet (cosP j) := by
    apply Perm.ext
    intro a
    apply Fin.eq_of_val_eq
    have hact := congrArg (fun q : Perm 120 => actP q (Blocks.blkSet a))
      (he.symm.trans he')
    rw [actP_comp, actP_comp,
      D28a_action (cosP_gauge i) a, D28a_action (cosP_gauge j) a,
      hk.2, hl.2] at hact
    have hidx := congrArg (blkOf Blocks.blkSet) hact
    rw [blkOf_blkSet, blkOf_blkSet] at hidx
    exact congrArg Fin.val hidx
  have hij := cosActionDistinct hi hj hp
  subst j
  refine ⟨?_, rfl⟩
  apply Perm.ext
  intro a
  have hcomp := congrArg (fun p : Perm 120 => p.toFun ((cosP i).invFun a))
    (he.symm.trans he')
  simpa only [Perm.comp_apply, Perm.right_inv] using hcomp

/-- `T56`.  The gauge group is the internal semidirect product of its normal
presentation kernel by the dihedral complement. -/
public theorem T56 :
    (∀ g k, D28 W0 g → stabPres Blocks.blkSet k →
      stabPres Blocks.blkSet (conjugate g k))
      ∧ (∀ g, D28 W0 g → ∃ k c, stabPres Blocks.blkSet k
        ∧ c ∈ cosList ∧ g = k.comp c)
      ∧ (∀ g k c l d, stabPres Blocks.blkSet k → c ∈ cosList →
        stabPres Blocks.blkSet l → d ∈ cosList →
        g = k.comp c → g = l.comp d → k = l ∧ c = d) :=
  ⟨(fun g k => witness_kernel_normal (g := g) (k := k)),
    (fun g => witness_factorisation (g := g)),
    fun _ _ _ _ _ => witness_factorisation_unique⟩

end UorAtlas.Closure

end
