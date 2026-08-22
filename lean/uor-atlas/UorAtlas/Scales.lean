module
public import Init
public import UorAtlas.Prelude.Algebra
public import UorAtlas.Prelude.NumInstances
public import UorAtlas.Prelude.Linear
public import UorAtlas.Prelude.Bitset
public import UorAtlas.Parameters
public import UorAtlas.Glue
public import UorAtlas.Roots
public import UorAtlas.Blocks

/-!
Section 17 of `UOR-ATLAS-FORMAL-001`: the scale, spectral and residue layer.
-/

set_option autoImplicit false
set_option maxRecDepth 40000

namespace UorAtlas.Scales

open UorAtlas.Prelude
open UorAtlas.Prelude.AddCommGroup
open UorAtlas.Prelude.CommRing
open UorAtlas.Prelude.Linear
open UorAtlas.Prelude.NumInstances
open UorAtlas.Roots
open UorAtlas.Blocks

/-! ## `D52`: orthogonality of classes -/

/-- `D52`. Two **distinct** classes are *orthogonal* when their representatives
are. In the `2x` scaling of `UorAtlas.Roots` this is `<u,v> = 0` on the nose;
the class is well defined because `<-u,v> = -<u,v>` vanishes with it. -/
@[expose] public def D52 (u v : K) : Prop := u ≠ v ∧ dot (rep u) (rep v) = 0

public instance D52.instDecidable (u v : K) : Decidable (D52 u v) :=
  inferInstanceAs (Decidable (u ≠ v ∧ dot (rep u) (rep v) = 0))

/-- Orthogonality on raw indices, the form the kernel runs. -/
@[expose] public def orthN (i j : Nat) : Bool :=
  !decide (i = j) && decide (dot8 (repN i) (repN j) = 0)

public theorem orthN_iff (u v : K) : orthN u.val v.val = true ↔ D52 u v := by
  rw [orthN, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · intro h
    exact ⟨fun he => by rw [congrArg Fin.val he] at h; exact absurd rfl (of_decide_eq_false h.1),
      of_decide_eq_true h.2⟩
  · intro h
    exact ⟨decide_eq_false (fun he => h.1 (Fin.eq_of_val_eq he)), decide_eq_true h.2⟩

/-- Orthogonality is the complement of adjacency on distinct classes. -/
public theorem D52_iff_not_D13 {u v : K} (h : u ≠ v) : D52 u v ↔ ¬ D13 u v := by
  have htri := allLt_true _ _ (allLt_true _ _ dotTri u.val u.isLt) v.val v.isLt
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at htri
  have hne : ¬ (u.val = v.val) := fun he => h (Fin.eq_of_val_eq he)
  have hd : dot (rep u) (rep v) = 0 ∨ dot (rep u) (rep v) = 4
      ∨ dot (rep u) (rep v) = -4 := by
    rcases htri with ((h1 | h1) | h1) | h1
    · exact absurd (of_decide_eq_true h1) hne
    · exact Or.inl (of_decide_eq_true h1)
    · exact Or.inr (Or.inl (of_decide_eq_true h1))
    · exact Or.inr (Or.inr (of_decide_eq_true h1))
  constructor
  · intro ho hadj
    rcases hadj.2 with hh | hh <;> rw [ho.2] at hh <;> exact absurd hh (by decide)
  · intro hn
    refine ⟨h, ?_⟩
    rcases hd with hh | hh | hh
    · exact hh
    · exact absurd ⟨h, Or.inl hh⟩ hn
    · exact absurd ⟨h, Or.inr hh⟩ hn

/-- Adjacency is the complement of orthogonality on distinct classes: the form
`S29` and `S30` read the class graph in. -/
public theorem D13_iff_not_D52 {u v : K} (h : u ≠ v) : D13 u v ↔ ¬ D52 u v := by
  constructor
  · intro hd ho; exact (D52_iff_not_D13 h).mp ho hd
  · intro hn
    by_cases hd : D13 u v
    · exact hd
    · exact absurd ((D52_iff_not_D13 h).mpr hd) hn

/-! ## `D54`, `D54a`: OrthFrames and OrthFramePartitions

An OrthFrame is a maximal-size pairwise-orthogonal subset of the object it sits
in: four classes inside a block, whose root span has rank `4` by `D16`, and
eight inside an AtlasInstance or inside `K`, whose span is all of `L`. An
OrthFramePartition cuts the object into such frames.

Both notions are checked, never searched: the frames are exhibited as numerals
computed outside and every clause is a `Bool` the kernel evaluates. -/

/-- The union of the first `k` members of a family of class subsets. -/
@[expose] public def unionUpto (f : Nat → Bitset) : Nat → Bitset
  | 0 => Bitset.empty
  | k + 1 => Bitset.union (f k) (unionUpto f k)

public theorem mem_unionUpto (f : Nat → Bitset) (i : Nat) :
    ∀ k, i ∈ unionUpto f k ↔ ∃ a, a < k ∧ i ∈ f a := by
  intro k
  induction k with
  | zero =>
    exact ⟨fun h => absurd h (Bitset.notMem_empty i), fun ⟨a, ha, _⟩ => absurd ha (by omega)⟩
  | succ n ih =>
    constructor
    · intro h
      rcases (Bitset.mem_union _ _ i).mp h with h1 | h1
      · exact ⟨n, Nat.lt_succ_self n, h1⟩
      · obtain ⟨a, ha, hm⟩ := ih.mp h1
        exact ⟨a, Nat.lt_succ_of_lt ha, hm⟩
    · intro ⟨a, ha, hm⟩
      refine (Bitset.mem_union _ _ i).mpr ?_
      rcases Nat.lt_or_ge a n with hlt | hge
      · exact Or.inr (ih.mpr ⟨a, hlt, hm⟩)
      · have : a = n := by omega
        exact Or.inl (this ▸ hm)

/-- A class subset whose classes are pairwise orthogonal. -/
@[expose] public def PwOrth (F : Bitset) : Prop :=
  ∀ u v : K, u.val ∈ F → v.val ∈ F → u ≠ v → D52 u v

/-- Pairwise orthogonality as one `Bool`, run over the members of `F` rather
than over all of `K`, so the cost is `|F|^2` inner products. -/
@[expose] public def pwOrthOK (F : Bitset) : Bool :=
  (Bitset.toList F).all (fun i => (Bitset.toList F).all (fun j => decide (i = j) || orthN i j))

public theorem pwOrth_of {F : Bitset} (h : pwOrthOK F = true) : PwOrth F := by
  intro u v hu hv hne
  have hu' : u.val ∈ Bitset.toList F := (Bitset.mem_toList F u.val).mpr hu
  have hv' : v.val ∈ Bitset.toList F := (Bitset.mem_toList F v.val).mpr hv
  have h1 := List.all_eq_true.mp h u.val hu'
  have h2 := List.all_eq_true.mp h1 v.val hv'
  rw [Bool.or_eq_true] at h2
  rcases h2 with h3 | h3
  · exact absurd (Fin.eq_of_val_eq (of_decide_eq_true h3)) hne
  · exact (orthN_iff u v).mp h3

/-- `D54`. An **OrthFrame** of the class subset `S`: a subset of `S` of size
`n` whose classes are pairwise orthogonal. -/
@[expose] public def D54 (S F : Bitset) (n : Nat) : Prop :=
  Bitset.subset F S = true ∧ Bitset.card F = n ∧ PwOrth F

/-- `D54a`. An **OrthFramePartition** of `S`: `k` pairwise-disjoint OrthFrames
of `S`, each of size `n`, whose union is `S`. -/
public structure D54a (S : Bitset) (k n : Nat) where
  part : Nat → Bitset
  isFrame : ∀ a, a < k → D54 S (part a) n
  disjoint : ∀ a b, a < k → b < k → a ≠ b → Bitset.inter (part a) (part b) = Bitset.empty
  covers : unionUpto part k = S

/-- The whole certificate as one `Bool`. -/
@[expose] public def partOK (S : Bitset) (f : Nat → Bitset) (k n : Nat) : Bool :=
  allLt (fun a => Bitset.subset (f a) S && decide (Bitset.card (f a) = n) && pwOrthOK (f a)) k
    && allLt (fun a => allLt (fun b => decide (a = b)
        || decide (Bitset.inter (f a) (f b) = Bitset.empty)) k) k
    && decide (unionUpto f k = S)

@[expose] public def partition_of_partOK {S : Bitset} {f : Nat → Bitset} {k n : Nat}
    (h : partOK S f k n = true) : D54a S k n where
  part := f
  isFrame := by
    intro a ha
    have h1 := allLt_true _ _ (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp h).1).1 a ha
    rw [Bool.and_eq_true, Bool.and_eq_true] at h1
    exact ⟨h1.1.1, of_decide_eq_true h1.1.2, pwOrth_of h1.2⟩
  disjoint := by
    intro a b ha hb hab
    have h1 := allLt_true _ _ (allLt_true _ _
      (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp h).1).2 a ha) b hb
    rw [Bool.or_eq_true] at h1
    rcases h1 with h2 | h2
    · exact absurd (of_decide_eq_true h2) hab
    · exact of_decide_eq_true h2
  covers := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp h).2

/-! ### The exhibited frames

`frameAt` reads a `128`-bit slot out of a packed table, the same encoding
`repTable` uses for the class representatives. Nothing about the tables is
asserted: `partOK` re-derives every clause from `dot`. -/

@[expose] public def frameAt (tab a : Nat) : Bitset :=
  Bitset.ofNat ((tab >>> (128 * a)) &&& (2 ^ 128 - 1))

/-- The three orthogonal quadruples of each of the four blocks of `A0`, block
`a` occupying slots `3a`, `3a+1`, `3a+2`. -/
@[expose] public def blkFrameTable : Nat :=
  29906455646170717342011688481546393058345367571805580626835795145525959454388267666177761637788128609400774175209867724455215864374628203868321537598801108933728221521615479530123658309384728506837635018131117271779760759519907921959407089593050602120132501303160763230485696675902609367628955829831396368293705812682568924117661846785284548113654118773506862775432187265796665424084931678806899811451396809328655818438132486789758516723715

/-- The six orthogonal `8`-frames of the AtlasInstance `V(A0)`. -/
@[expose] public def atlFrameTable : Nat :=
  568549156900838268823031202665455099684174433898473851107562935992023906333547861899702534679782399521187349698369326886283499211671138899511425620715975127724349539488514029767895868489914103045037526296708081651928998306906115

/-- The fifteen orthogonal `8`-frames of `K`. -/
@[expose] public def kFrameTable : Nat :=
  186939668303413809897015026125552929244363205598639176989556877391131410555294947318005804540385487964997879641969802131298514347250991876014864315465483538619742119672056460786373932017274784267401983217587797902533847187330109696525490749273706847385777422298180196400027391432212019451236406044473264440403248286255207868577091697035320564723879076745796613645139328786693273481972865305895030035881626169134378207817865110465963912176743637532881209087044458922523425856916684296347871045717550398385825013041881285490501596186582210392858908185550717490556685514149199875

/-- `K` itself as a class subset: every index below `120`. -/
@[expose] public def fullK : Bitset := Bitset.ofNat (2 ^ 120 - 1)

public theorem mem_fullK (i : Nat) : i ∈ fullK ↔ i < 120 := by
  show Nat.testBit (2 ^ 120 - 1) i = true ↔ i < 120
  rw [Nat.testBit_two_pow_sub_one]
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-! ## `S1`, `S2`, `S6`, `S7`, `S8`: the frame decompositions

`S1` and `S29` are the same fact read in complementary directions, which is why
`D52_iff_not_D13` is proved once above: inside a block, two distinct classes
are orthogonal exactly when they are non-adjacent, so a decomposition of the
orthogonality graph into cliques is a decomposition of the class graph into the
parts of a complete multipartite graph.

Scope. `S1`, `S2`, `S6`, `S7`, `S29` and `S30` are statements about the
exhibited AtlasPresentation `A0` of `UorAtlas.Blocks`, in exactly the sense in
which `T14`-`T19` are; their declaration types deliberately record that scope.
The completed block and AtlasInstance populations are handled by the census
and closure modules. `S8` is about `K` itself and is unconditional. -/

/-- The three quadruples of block `a`, slots `3a`, `3a+1`, `3a+2` of the
table. -/
@[expose] public def blkFrame (a : Nat) : Nat → Bitset := fun t => frameAt blkFrameTable (3 * a + t)

/-- No orthogonal pair crosses two parts: this is what makes the parts the
connected components of the orthogonality graph, rather than merely three
cliques inside it. -/
@[expose] public def crossOK (f : Nat → Bitset) (k : Nat) : Bool :=
  allLt (fun s => allLt (fun t => decide (s = t)
    || (Bitset.toList (f s)).all (fun i =>
        (Bitset.toList (f t)).all (fun j => !orthN i j))) k) k

public theorem cross_of_crossOK {f : Nat → Bitset} {k : Nat} (h : crossOK f k = true)
    {s t : Nat} (hs : s < k) (ht : t < k) (hst : s ≠ t) {u v : K}
    (hu : u.val ∈ f s) (hv : v.val ∈ f t) : ¬ D52 u v := by
  have h1 := allLt_true _ _ (allLt_true _ _ h s hs) t ht
  rw [Bool.or_eq_true] at h1
  rcases h1 with h2 | h2
  · exact absurd (of_decide_eq_true h2) hst
  · have hu' : u.val ∈ Bitset.toList (f s) := (Bitset.mem_toList (f s) u.val).mpr hu
    have hv' : v.val ∈ Bitset.toList (f t) := (Bitset.mem_toList (f t) v.val).mpr hv
    have h3 := List.all_eq_true.mp (List.all_eq_true.mp h2 u.val hu') v.val hv'
    intro ho
    rw [Bool.not_eq_true', (orthN_iff u v).mpr ho] at h3
    exact absurd h3 (by decide)

/-- The one kernel computation behind `S1`, `S2`, `S6` and `S29`: each of the
four blocks of `A0` splits into three orthogonal quadruples with no
orthogonality across parts. -/
public theorem blkFrameComp : allFin (fun a : Fin 4 =>
    partOK (blkSet a) (blkFrame a.val) 3 4 && crossOK (blkFrame a.val) 3) = true := by
  decide +kernel

public theorem blkFrameFacts (a : Fin 4) :
    partOK (blkSet a) (blkFrame a.val) 3 4 = true ∧ crossOK (blkFrame a.val) 3 = true := by
  have h := allFin_true _ blkFrameComp a
  rw [Bool.and_eq_true] at h
  exact h

/-- The OrthFramePartition of block `a` of `A0`. -/
@[expose] public def blkPart (a : Fin 4) : D54a (blkSet a) 3 4 :=
  partition_of_partOK (blkFrameFacts a).1

public theorem blkPart_part (a : Fin 4) : (blkPart a).part = blkFrame a.val := rfl

/-- `S1`. The orthogonality graph of a block is three `4`-cliques: three
disjoint quadruples of pairwise-orthogonal classes, covering the block, with no
orthogonal pair crossing two of them. -/
public theorem S1 (a : Fin 4) :
    (∀ t, t < 3 → Bitset.card ((blkPart a).part t) = 4 ∧ PwOrth ((blkPart a).part t))
      ∧ unionUpto (blkPart a).part 3 = blkSet a
      ∧ ∀ (s t : Nat) (u v : K), s < 3 → t < 3 → s ≠ t →
          u.val ∈ (blkPart a).part s → v.val ∈ (blkPart a).part t → ¬ D52 u v := by
  refine ⟨fun t ht => ⟨((blkPart a).isFrame t ht).2.1, ((blkPart a).isFrame t ht).2.2⟩,
    (blkPart a).covers, fun s t u v hs ht hst hu hv => ?_⟩
  rw [blkPart_part] at hu hv
  exact cross_of_crossOK (blkFrameFacts a).2 hs ht hst hu hv

/-- `S2`. That count is the scale `T`: `T = 3` by `T2`, and a block's `stride/2
= 12` classes are exactly `T` orthogonal quadruples. -/
public theorem S2 : Parameters.D3 = 3
    ∧ ∀ a : Fin 4, Bitset.card (blkSet a) = Parameters.D3 * 4 := by
  refine ⟨Parameters.T2.left, fun a => ?_⟩
  rw [Parameters.T2.left, (blkIsBlock a).2.1]

/-- `S6`. A block carries an OrthFramePartition of size `3`. -/
public theorem S6 (a : Fin 4) : Nonempty (D54a (blkSet a) 3 4) := ⟨blkPart a⟩

/-! ### The AtlasInstance the kernel can evaluate

`A0` of `UorAtlas.Blocks` is not an exposed definition, so `V A0` does not
reduce outside that module. `atlSet` is the same class subset written out of
the exposed `blkSet`, and `atl_atlSet` re-establishes that it is an
AtlasInstance from the exposed `frm03`, `frm12` and `tightComp`. Everything
below that speaks about "the AtlasInstance" speaks about this one. -/

/-- The support of the witness AtlasPresentation, as a subset the kernel
evaluates. -/
@[expose] public def atlSet : Bitset := union4 blkSet

/-- `atlSet` is an AtlasInstance: it is the union of the two disjoint
BlockFrames `{B_0,B_3}` and `{B_1,B_2}`, and it is tight. -/
public theorem atl_atlSet : Atl atlSet :=
  ⟨blkSet 0, blkSet 3, blkSet 1, blkSet 2, frm03, frm12, by decide +kernel, by decide +kernel,
    tight_of_tightOK tightComp⟩

/-- The kernel computation behind `S7`: the six orthogonal `8`-frames of the
AtlasInstance. -/
public theorem atlFrameComp : partOK atlSet (frameAt atlFrameTable) 6 8 = true := by
  decide +kernel

/-- `S7`. An AtlasInstance carries an OrthFramePartition of size `6`. -/
public theorem S7 : Nonempty (D54a atlSet 6 8) := ⟨partition_of_partOK atlFrameComp⟩

/-- The kernel computation behind `S8`: the fifteen orthogonal `8`-frames of
`K`. -/
public theorem kFrameComp : partOK fullK (frameAt kFrameTable) 15 8 = true := by
  decide +kernel

/-- `S8`. `K` carries an OrthFramePartition of size `15`. -/
public theorem S8 : Nonempty (D54a fullK 15 8) := ⟨partition_of_partOK kFrameComp⟩


/-! ## `S9`: an OrthFramePartition counts the object

`S9` is the one statement of this section that is not a kernel computation.
The parts of an OrthFramePartition are disjoint and cover, so their sizes add:
`|S| = k * n`. The number of parts is therefore `|S|` divided by the common
frame size -- which is the rank of the span of `S`, `4` inside a block and `8`
inside an AtlasInstance or inside `K` -- and is not a free parameter of the
construction. -/

/-- A frame is disjoint from the union of the frames before it. This is what
turns the covering clause of `D54a` into an addition. -/
public theorem unionUpto_disj {f : Nat → Bitset} {k : Nat}
    (hd : ∀ a b, a < k → b < k → a ≠ b → Bitset.inter (f a) (f b) = Bitset.empty)
    {m : Nat} (hm : m < k) : Bitset.inter (f m) (unionUpto f m) = Bitset.empty := by
  refine Bitset.ext (fun i => ⟨fun h => ?_, fun h => absurd h (Bitset.notMem_empty i)⟩)
  obtain ⟨h1, h2⟩ := (Bitset.mem_inter _ _ i).mp h
  obtain ⟨a, ha, hia⟩ := (mem_unionUpto f i m).mp h2
  exact (disj_mem (hd m a hm (Nat.lt_trans ha hm) (fun he => by omega)) h1 hia).elim

/-- The union of the first `m` frames has `m * n` classes. -/
public theorem card_unionUpto {f : Nat → Bitset} {k n : Nat}
    (hd : ∀ a b, a < k → b < k → a ≠ b → Bitset.inter (f a) (f b) = Bitset.empty)
    (hc : ∀ a, a < k → Bitset.card (f a) = n) :
    ∀ m, m ≤ k → Bitset.card (unionUpto f m) = m * n := by
  intro m
  induction m with
  | zero =>
    intro _
    show Bitset.card Bitset.empty = 0 * n
    rw [Bitset.card_empty]
    omega
  | succ p ih =>
    intro hp
    have hpk : p < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self p) hp
    have hih := ih (Nat.le_of_lt hpk)
    show Bitset.card (Bitset.union (f p) (unionUpto f p)) = (p + 1) * n
    rw [card_union_disj (unionUpto_disj hd hpk), hc p hpk, hih, Nat.succ_mul]
    omega

/-- `S9`. An OrthFramePartition of `S` into `k` OrthFrames of `n` classes each
has `|S| = k * n`. -/
public theorem S9 {S : Bitset} {k n : Nat} (p : D54a S k n) : Bitset.card S = k * n := by
  rw [← p.covers]
  exact card_unionUpto (fun a b => p.disjoint a b) (fun a ha => (p.isFrame a ha).2.1) k
    (Nat.le_refl k)

/-- `K` has `120` classes, the count `S9` reads the fifteen `8`-frames
against. -/
public theorem card_fullK : Bitset.card fullK = 120 := by decide +kernel

/-! ## `S3`, `S4`, `S5`: the rank-8 orthogonality graph is connected

Inside a block the orthogonality graph falls apart, and `S1` says how: three
`4`-cliques with no orthogonal pair between them, so there the parts of the
partition really are the connected components. At rank `8` that stops being
true. The orthogonality graph of `K`, and the one induced on an AtlasInstance,
are each connected, so the component decomposition is the one-part
decomposition and gives no partition at all. `S5` is that reading: a partition
of `K` across which no orthogonal pair runs has a single nonempty part, so the
fifteen frames of `S8` and the six of `S7` are exhibited data and cannot be
read off the graph. -/

/-- Orthogonality is symmetric, because `<u,v> = <v,u>`. -/
public theorem D52.symm {u v : K} (h : D52 u v) : D52 v u :=
  ⟨fun he => h.1 he.symm, by rw [dot_comm]; exact h.2⟩

/-- The orthogonal neighbours of `i` among the indices below `k`. -/
@[expose] public def orthNbr (i : Nat) : Nat → Bitset
  | 0 => Bitset.empty
  | k + 1 => if orthN i k then Bitset.insert (orthNbr i k) k else orthNbr i k

public theorem mem_orthNbr (i j : Nat) :
    ∀ k, j ∈ orthNbr i k ↔ j < k ∧ orthN i j = true := by
  intro k
  induction k with
  | zero => exact ⟨fun h => absurd h (Bitset.notMem_empty j), fun h => absurd h.1 (by omega)⟩
  | succ m ih =>
    by_cases hm : orthN i m = true
    · have he : orthNbr i (m + 1) = Bitset.insert (orthNbr i m) m := if_pos hm
      rw [he, Bitset.mem_insert]
      constructor
      · intro h
        rcases h with h | h
        · exact ⟨by omega, by rw [h]; exact hm⟩
        · exact ⟨Nat.lt_succ_of_lt (ih.mp h).1, (ih.mp h).2⟩
      · intro h
        rcases Nat.lt_or_ge j m with hlt | hge
        · exact Or.inr (ih.mpr ⟨hlt, h.2⟩)
        · exact Or.inl (by omega)
    · have he : orthNbr i (m + 1) = orthNbr i m := if_neg hm
      rw [he, ih]
      constructor
      · intro h; exact ⟨Nat.lt_succ_of_lt h.1, h.2⟩
      · intro h
        rcases Nat.lt_or_ge j m with hlt | hge
        · exact ⟨hlt, h.2⟩
        · have hj : j = m := by omega
          exact absurd (hj ▸ h.2) hm

/-- One breadth-first step inside `S`: the members of `T` with index below `k`,
together with the orthogonal neighbours of each that lie in `S`. -/
@[expose] public def stepIn (S T : Bitset) : Nat → Bitset
  | 0 => T
  | k + 1 =>
    if k ∈ T then Bitset.union (Bitset.inter (orthNbr k 120) S) (stepIn S T k) else stepIn S T k

/-- The classes of `S` reachable from `c` in at most `n` orthogonal steps. -/
@[expose] public def reachIn (S : Bitset) (c : Nat) : Nat → Bitset
  | 0 => Bitset.inter (Bitset.singleton c) S
  | n + 1 => stepIn S (reachIn S c n) 120

/-- `u` and `v` are joined by a chain of orthogonal steps that never leaves
`S`: connectivity of the orthogonality graph induced on `S`. -/
public inductive ConnIn (S : Bitset) (u : K) : K → Prop
  | refl : u.val ∈ S → ConnIn S u u
  | step {v w : K} : ConnIn S u v → w.val ∈ S → D52 v w → ConnIn S u w

public theorem ConnIn.mem_src {S : Bitset} {u v : K} (h : ConnIn S u v) : u.val ∈ S := by
  induction h with
  | refl hu => exact hu
  | step _ _ _ ih => exact ih

public theorem ConnIn.mem_tgt {S : Bitset} {u v : K} (h : ConnIn S u v) : v.val ∈ S := by
  cases h with
  | refl hu => exact hu
  | step _ hw _ => exact hw

public theorem ConnIn.trans {S : Bitset} {u v w : K}
    (h1 : ConnIn S u v) (h2 : ConnIn S v w) : ConnIn S u w := by
  induction h2 with
  | refl _ => exact h1
  | step _ hw hd ih => exact ConnIn.step ih hw hd

public theorem ConnIn.symm {S : Bitset} {u v : K} (h : ConnIn S u v) : ConnIn S v u := by
  induction h with
  | refl hu => exact ConnIn.refl hu
  | step hc hw hd ih =>
    exact ConnIn.trans (ConnIn.step (ConnIn.refl hw) (ConnIn.mem_tgt hc) (D52.symm hd)) ih

/-- Class `0`, the base point every breadth-first search below starts from. -/
@[expose] public def c0 : K := ⟨0, by decide⟩

public theorem stepIn_lt {S T : Bitset} (hT : ∀ j, j ∈ T → j < 120) :
    ∀ k, ∀ j, j ∈ stepIn S T k → j < 120 := by
  intro k
  induction k with
  | zero => exact hT
  | succ m ih =>
    intro j hj
    by_cases hm : m ∈ T
    · have he : stepIn S T (m + 1)
          = Bitset.union (Bitset.inter (orthNbr m 120) S) (stepIn S T m) := if_pos hm
      rw [he] at hj
      rcases (Bitset.mem_union _ _ j).mp hj with h1 | h1
      · exact ((mem_orthNbr m j 120).mp ((Bitset.mem_inter _ _ j).mp h1).1).1
      · exact ih j h1
    · have he : stepIn S T (m + 1) = stepIn S T m := if_neg hm
      rw [he] at hj
      exact ih j hj

public theorem conn_stepIn {S T : Bitset} {c : K}
    (hT : ∀ j : K, j.val ∈ T → ConnIn S c j) (hTlt : ∀ j, j ∈ T → j < 120) :
    ∀ k, ∀ j : K, j.val ∈ stepIn S T k → ConnIn S c j := by
  intro k
  induction k with
  | zero => exact hT
  | succ m ih =>
    intro j hj
    by_cases hm : m ∈ T
    · have he : stepIn S T (m + 1)
          = Bitset.union (Bitset.inter (orthNbr m 120) S) (stepIn S T m) := if_pos hm
      rw [he] at hj
      rcases (Bitset.mem_union _ _ j.val).mp hj with h1 | h1
      · obtain ⟨h2, h3⟩ := (Bitset.mem_inter _ _ j.val).mp h1
        have hmlt : m < 120 := hTlt m hm
        exact ConnIn.step (hT ⟨m, hmlt⟩ hm) h3
          ((orthN_iff ⟨m, hmlt⟩ j).mp ((mem_orthNbr m j.val 120).mp h2).2)
      · exact ih j h1
    · have he : stepIn S T (m + 1) = stepIn S T m := if_neg hm
      rw [he] at hj
      exact ih j hj

public theorem reachIn_lt {S : Bitset} {c : K} :
    ∀ n, ∀ j, j ∈ reachIn S c.val n → j < 120 := by
  intro n
  induction n with
  | zero =>
    intro j hj
    have h1 := ((Bitset.mem_inter _ _ j).mp hj).1
    rw [Bitset.mem_singleton] at h1
    rw [h1]
    exact c.isLt
  | succ m ih => exact stepIn_lt ih 120

public theorem conn_reachIn {S : Bitset} {c : K} (hc : c.val ∈ S) :
    ∀ n, ∀ j : K, j.val ∈ reachIn S c.val n → ConnIn S c j := by
  intro n
  induction n with
  | zero =>
    intro j hj
    have h1 := ((Bitset.mem_inter _ _ j.val).mp hj).1
    rw [Bitset.mem_singleton] at h1
    have hjc : j = c := Fin.eq_of_val_eq h1
    rw [hjc]
    exact ConnIn.refl hc
  | succ m ih => exact conn_stepIn ih (reachIn_lt m) 120

/-- One orthogonal step out of class `0` reaches its `63` orthogonal
neighbours. Naming the intermediate set keeps the second step from
re-deriving the first for every index it scans. -/
public theorem reach1Comp :
    reachIn fullK c0.val 1
      = Bitset.ofNat 1329227995475430863154519585526382595 := by decide +kernel

/-- The kernel computation behind `S3`: a second orthogonal step reaches every
class. -/
public theorem reachComp : reachIn fullK c0.val 2 = fullK := by
  show stepIn fullK (reachIn fullK c0.val 1) 120 = fullK
  rw [reach1Comp]
  decide +kernel

/-- One orthogonal step out of class `0` inside the AtlasInstance reaches its
`27` orthogonal neighbours there. -/
public theorem reachAtl1Comp :
    reachIn atlSet c0.val 1
      = Bitset.ofNat 125104765790634370331535696684122115 := by decide +kernel

/-- The kernel computation behind `S4`: a second step, still inside the
AtlasInstance, reaches all `48` of its classes. -/
public theorem reachAtlComp : reachIn atlSet c0.val 2 = atlSet := by
  show stepIn atlSet (reachIn atlSet c0.val 1) 120 = atlSet
  rw [reachAtl1Comp]
  decide +kernel

public theorem c0_mem_atlSet : c0.val ∈ atlSet := by decide +kernel

/-- `S3`. The orthogonality graph of `K` is connected. -/
public theorem S3 : ∀ u v : K, ConnIn fullK u v := by
  have hc : c0.val ∈ fullK := (mem_fullK 0).mpr (by decide)
  have key : ∀ j : K, ConnIn fullK c0 j := fun j =>
    conn_reachIn hc 2 j (by rw [reachComp]; exact (mem_fullK j.val).mpr j.isLt)
  exact fun u v => ConnIn.trans (key u).symm (key v)

/-- `S4`. The orthogonality graph induced on the AtlasInstance is connected. -/
public theorem S4 : ∀ u v : K, u.val ∈ atlSet → v.val ∈ atlSet → ConnIn atlSet u v := by
  have key : ∀ j : K, j.val ∈ atlSet → ConnIn atlSet c0 j := fun j hj =>
    conn_reachIn c0_mem_atlSet 2 j (by rw [reachAtlComp]; exact hj)
  exact fun u v hu hv => ConnIn.trans (key u hu).symm (key v hv)

/-- `S5`. Connectivity read as a statement about partitions: if the parts of a
covering of `K` are never joined by an orthogonal pair, then every nonempty
part is all of `K`. The fifteen frames of `S8` are therefore not the components
of the orthogonality graph, and no partition of `K` into more than one part can
be obtained from them. -/
public theorem S5 {f : Nat → Bitset} {k : Nat}
    (hcov : unionUpto f k = fullK) (hcross : crossOK f k = true)
    {a : Nat} (ha : a < k) {u : K} (hu : u.val ∈ f a) : f a = fullK := by
  have hstay : ∀ v : K, ConnIn fullK u v → v.val ∈ f a := by
    intro v hv
    induction hv with
    | refl _ => exact hu
    | @step v' w hc hw hd ih =>
      have hw' : w.val ∈ unionUpto f k := by rw [hcov]; exact hw
      obtain ⟨b, hb, hwb⟩ := (mem_unionUpto f w.val k).mp hw'
      by_cases hab : a = b
      · rw [hab]; exact hwb
      · exact absurd hd (cross_of_crossOK hcross ha hb hab ih hwb)
  refine Bitset.ext (fun i => ⟨fun h => ?_, fun h => ?_⟩)
  · rw [← hcov]
    exact (mem_unionUpto f i k).mpr ⟨a, ha, h⟩
  · exact hstay ⟨i, (mem_fullK i).mp h⟩ (S3 u ⟨i, (mem_fullK i).mp h⟩)


/-- `S29`. The class graph of a block is the complete tripartite graph
`K_{4,4,4}` on the three quadruples of `S1`: two distinct classes of a block
are adjacent exactly when they lie in different quadruples. -/
public theorem S29 (a : Fin 4) :
    ∀ (s t : Nat) (u v : K), s < 3 → t < 3 →
      u.val ∈ (blkPart a).part s → v.val ∈ (blkPart a).part t → u ≠ v →
      (D13 u v ↔ s ≠ t) := by
  intro s t u v hs ht hu hv hne
  constructor
  · intro hd hst
    subst hst
    exact (D52_iff_not_D13 hne).mp
      (((blkPart a).isFrame s hs).2.2 u v hu hv hne) hd
  · intro hst
    rw [blkPart_part] at hu hv
    exact (D13_iff_not_D52 hne).mpr (cross_of_crossOK (blkFrameFacts a).2 hs ht hst hu hv)

/-! ## `S30`: the class graph of a BlockFrame

Unlike everything else in this section, this one is about *every* BlockFrame:
`Frm` already carries the no-edge condition, and `D52_iff_not_D13` upgrades it
from "no edge" to "orthogonal". -/

/-- `S30`. The class graph of a BlockFrame is the disjoint union of the two
block graphs: every edge inside `V(F)` has both ends in the same block, and
every cross pair is orthogonal. -/
public theorem S30 (F : D46a) :
    (∀ u v : K, u.val ∈ F.V → v.val ∈ F.V → D13 u v →
        (u.val ∈ F.fst ∧ v.val ∈ F.fst) ∨ (u.val ∈ F.snd ∧ v.val ∈ F.snd))
      ∧ (∀ u v : K, u.val ∈ F.fst → v.val ∈ F.snd → D52 u v) := by
  obtain ⟨_, _, hdisj, hno⟩ := F.isFrm
  have hcross : ∀ u v : K, u.val ∈ F.fst → v.val ∈ F.snd → D52 u v := by
    intro u v hu hv
    have hne : u ≠ v := by
      intro he
      exact disj_mem hdisj hu (by rw [congrArg Fin.val he]; exact hv)
    exact (D52_iff_not_D13 hne).mpr (hno u v hu hv)
  refine ⟨fun u v hu hv hd => ?_, hcross⟩
  rcases (Bitset.mem_union _ _ u.val).mp hu with h1 | h1 <;>
    rcases (Bitset.mem_union _ _ v.val).mp hv with h2 | h2
  · exact Or.inl ⟨h1, h2⟩
  · exact absurd (hcross u v h1 h2) (fun ho => (D52_iff_not_D13 ho.1).mp ho hd)
  · exact absurd (hcross v u h2 h1)
      (fun ho => (D52_iff_not_D13 ho.1).mp ho ⟨fun he => hd.1 he.symm,
        by rw [dot_comm]; exact hd.2⟩)
  · exact Or.inr ⟨h1, h2⟩

/-! ## `S22`: the residue, and the `20 + 36 = 32 + 24 = 56` split -/

/-- The **residue** of a class subset: the classes of `K` it omits. -/
@[expose] public def residue (W : Bitset) : Bitset := Bitset.diff fullK W

public theorem mem_residue {W : Bitset} (v : K) : v.val ∈ residue W ↔ v.val ∉ W := by
  rw [show residue W = Bitset.diff fullK W from rfl, Bitset.mem_diff]
  exact ⟨fun h => h.2, fun h => ⟨(mem_fullK v.val).mpr v.isLt, h⟩⟩

/-- Adjacency is symmetric, which is what lets a degree counted along rows be
counted along columns. -/
public theorem A_comm (u v : K) : A u v = A v u := by
  by_cases h : u.val = v.val
  · show adjN u.val v.val = adjN v.val u.val
    rw [h]
  · have h' : ¬ (v.val = u.val) := fun hh => h (Eq.symm hh)
    show (if u.val = v.val then 0
        else if u.val < v.val then adjRaw u.val v.val else adjRaw v.val u.val)
      = (if v.val = u.val then 0
        else if v.val < u.val then adjRaw v.val u.val else adjRaw u.val v.val)
    rw [if_neg h, if_neg h']
    by_cases h2 : u.val < v.val
    · rw [if_pos h2, if_neg (show ¬ v.val < u.val from by omega)]
    · rw [if_neg h2, if_pos (show v.val < u.val from by omega)]

/-- Every class is counted once, inside `W` or in its residue: the degree
splits. -/
public theorem deg_split (W : Bitset) (v : K) : D14 W v + D14 (residue W) v = deg v := by
  have hsum : Vec.sumNat (fun u : K => (if u.val ∈ W then A u v else 0)
      + (if u.val ∈ residue W then A u v else 0)) = Vec.sumNat (fun u : K => A v u) := by
    refine Vec.sumNat_congr (fun u => ?_)
    by_cases hu : u.val ∈ W
    · rw [if_pos hu, if_neg (fun hh => ((mem_residue u).mp hh) hu), Nat.add_zero, A_comm]
    · rw [if_neg hu, if_pos ((mem_residue u).mpr hu), Nat.zero_add, A_comm]
  show Vec.sumNat (fun u : K => if u.val ∈ W then A u v else 0)
    + Vec.sumNat (fun u : K => if u.val ∈ residue W then A u v else 0) = deg v
  rw [← Vec.sumNat_add]
  exact hsum

/-- `S22`. A class of the AtlasInstance has `20` neighbours inside it and `36`
outside; a class of the residue has `32` inside the residue and `24` in the
AtlasInstance; and `20 + 36 = 32 + 24 = 56` is `T7`. -/
public theorem S22 :
    (∀ v : K, v.val ∈ atlSet → D14 atlSet v = 20 ∧ D14 (residue atlSet) v = 36)
      ∧ (∀ v : K, v.val ∈ residue atlSet →
          D14 (residue atlSet) v = 32 ∧ D14 atlSet v = 24)
      ∧ 20 + 36 = 56 ∧ 32 + 24 = 56 := by
  have htight : D15 atlSet := tight_of_tightOK tightComp
  refine ⟨fun v hv => ?_, fun v hv => ?_, rfl, rfl⟩
  · have h1 : D14 atlSet v = 20 := htight.1 v hv
    have h2 := deg_split atlSet v
    rw [h1, T7 v] at h2
    exact ⟨h1, by omega⟩
  · have hnot : v.val ∉ atlSet := (mem_residue v).mp hv
    have h1 : D14 atlSet v = 24 := htight.2 v hnot
    have h2 := deg_split atlSet v
    rw [h1, T7 v] at h2
    exact ⟨by omega, h1⟩

/-! ## `S28`: the quadratic the strongly regular parameters give -/

/-- `S28`. `T8` gives the class graph the parameters `(120, 56, 28, 24)`, so
its non-principal eigenvalues satisfy `x^2 - (lambda - mu) x - (k - mu) = 0`,
that is `x^2 - 4x - 32`. Its discriminant is `(lambda - mu)^2 + 4(k - mu) = 144
= 12^2`, so the roots are integers, and they are `8` and `-4` -- the two
factors `T9a` annihilates `A` with. -/
public theorem S28 :
    (∀ x : Int, x * x - ((28 : Int) - 24) * x - ((56 : Int) - 24)
        = (x - 8) * (x + 4))
      ∧ ((28 : Int) - 24) * ((28 : Int) - 24) + 4 * ((56 : Int) - 24) = 12 * 12
      ∧ (8 : Int) * 8 - 4 * 8 - 32 = 0
      ∧ (-4 : Int) * (-4) - 4 * (-4) - 32 = 0 := by
  refine ⟨fun x => ?_, by decide, by decide, by decide⟩
  show x * x - 4 * x - 32 = (x - 8) * (x + 4)
  have h1 : (x - 8) * (x + 4) = x * (x + 4) - 8 * (x + 4) := Int.sub_mul x 8 (x + 4)
  have h2 : x * (x + 4) = x * x + x * 4 := Int.mul_add x x 4
  have h3 : (8 : Int) * (x + 4) = 8 * x + 8 * 4 := Int.mul_add 8 x 4
  have h4 : x * 4 = 4 * x := Int.mul_comm x 4
  rw [h1, h2, h3, h4]
  omega

/-! ## `S42`: the AtlasInstance graph, its order and its low traces

The `48` classes are enumerated in increasing order by `xIdx`, a byte table,
and `xClass` lifts that enumeration to `K`. `AX` is the induced adjacency
matrix, and the two traces are sums over `Fin 48` of products of its entries --
`tr(A^2) = sum_{i,j} A_ij A_ji` and `tr(A^3) = sum_{i,j,k} A_ij A_jk A_ki`. -/

/-- The `48` classes of the AtlasInstance in increasing order, one byte each. -/
@[expose] public def xIdxTable : Nat :=
  17923429779227654247475788590940897806682391243105031738009533080962623398245970192080746164103443061647390340677888

@[expose] public def xIdx (i : Nat) : Nat := (xIdxTable >>> (8 * i)) &&& 255

/-- The table lists members of the AtlasInstance, strictly increasing, and the
singletons it names exhaust the AtlasInstance. -/
public theorem xIdxComp :
    allLt (fun i => decide (xIdx i < 120) && Bitset.mem atlSet (xIdx i)) 48 = true
      ∧ allLt (fun i => decide (xIdx i < xIdx (i + 1))) 47 = true
      ∧ unionUpto (fun i => Bitset.singleton (xIdx i)) 48 = atlSet := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

public theorem xIdx_lt (i : Nat) (hi : i < 48) : xIdx i < 120 :=
  of_decide_eq_true (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ xIdxComp.1 i hi)).1

/-- The `i`-th class of the AtlasInstance. -/
@[expose] public def xClass (i : Fin 48) : K := ⟨xIdx i.val % 120, Nat.mod_lt _ (by decide)⟩

public theorem xClass_val (i : Fin 48) : (xClass i).val = xIdx i.val :=
  Nat.mod_eq_of_lt (xIdx_lt i.val i.isLt)

public theorem xClass_mem (i : Fin 48) : (xClass i).val ∈ atlSet := by
  rw [xClass_val]
  exact (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ xIdxComp.1 i.val i.isLt)).2

/-- Every class of the AtlasInstance is listed: the enumeration is onto. -/
public theorem xClass_onto {u : K} (h : u.val ∈ atlSet) : ∃ i : Fin 48, xClass i = u := by
  rw [← xIdxComp.2.2] at h
  obtain ⟨a, ha, hm⟩ := (mem_unionUpto _ _ 48).mp h
  refine ⟨⟨a, ha⟩, Fin.eq_of_val_eq ?_⟩
  rw [xClass_val]
  exact ((Bitset.mem_singleton u.val (xIdx a)).mp hm).symm

/-- The enumeration is injective, so it is a bijection onto the AtlasInstance. -/
public theorem xClass_inj {i j : Fin 48} (h : xClass i = xClass j) : i = j := by
  have hmono : ∀ a b : Nat, a < b → b < 48 → xIdx a < xIdx b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ c ih =>
      have hstep : xIdx c < xIdx (c + 1) :=
        of_decide_eq_true (allLt_true _ _ xIdxComp.2.1 c (by omega))
      rcases Nat.lt_or_ge a c with hlt | hge
      · exact Nat.lt_trans (ih hlt (by omega)) hstep
      · have : a = c := by omega
        exact this ▸ hstep
  have hval : xIdx i.val = xIdx j.val := by
    have := congrArg Fin.val h
    rw [xClass_val, xClass_val] at this
    exact this
  refine Fin.eq_of_val_eq ?_
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact absurd hval (by have := hmono i.val j.val hlt j.isLt; omega)
  · exact heq
  · exact absurd hval (by have := hmono j.val i.val hgt i.isLt; omega)

/-- The adjacency matrix of the class graph induced on the AtlasInstance. -/
@[expose] public def AX (i j : Fin 48) : Nat := A (xClass i) (xClass j)

/-- The same matrix on raw indices, the form the kernel runs. -/
@[expose] public def aX (i j : Nat) : Nat := adjN (xIdx i) (xIdx j)

public theorem AX_eq_aX (i j : Fin 48) : AX i j = aX i.val j.val := by
  show adjN (xClass i).val (xClass j).val = adjN (xIdx i.val) (xIdx j.val)
  rw [xClass_val, xClass_val]

@[expose] public def trX2N : Nat := sumN (fun i => sumN (fun k => aX i k * aX k i) 48) 48

@[expose] public def trX3N : Nat :=
  sumN (fun i => sumN (fun j => sumN (fun k => aX i j * aX j k * aX k i) 48) 48) 48

public theorem trXComp : trX2N = 960 ∧ trX3N = 8448 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- `S42`. The AtlasInstance has `|X| = 48` classes, and the graph it induces
has `tr(A_X^2) = 960` and `tr(A_X^3) = 8448`. -/
public theorem S42 :
    Bitset.card atlSet = 48
      ∧ Vec.sumNat (fun i : Fin 48 => Vec.sumNat (fun k : Fin 48 => AX i k * AX k i)) = 960
      ∧ Vec.sumNat (fun i : Fin 48 => Vec.sumNat (fun j : Fin 48 =>
          Vec.sumNat (fun k : Fin 48 => AX i j * AX j k * AX k i))) = 8448 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · have h1 : Vec.sumNat (fun i : Fin 48 => Vec.sumNat (fun k : Fin 48 => AX i k * AX k i))
        = Vec.sumNat (fun i : Fin 48 => (fun a => sumN (fun k => aX a k * aX k a) 48) i.val) := by
      refine Vec.sumNat_congr (fun i => ?_)
      have h2 : Vec.sumNat (fun k : Fin 48 => AX i k * AX k i)
          = Vec.sumNat (fun k : Fin 48 => (fun c => aX i.val c * aX c i.val) k.val) := by
        refine Vec.sumNat_congr (fun k => ?_)
        rw [AX_eq_aX, AX_eq_aX]
      rw [h2]
      exact sumNat_eq_sumN 48 (fun c => aX i.val c * aX c i.val)
    rw [h1, sumNat_eq_sumN 48 (fun a => sumN (fun k => aX a k * aX k a) 48)]
    exact trXComp.1
  · have h1 : Vec.sumNat (fun i : Fin 48 => Vec.sumNat (fun j : Fin 48 =>
          Vec.sumNat (fun k : Fin 48 => AX i j * AX j k * AX k i)))
        = Vec.sumNat (fun i : Fin 48 =>
            (fun a => sumN (fun b => sumN (fun c => aX a b * aX b c * aX c a) 48) 48) i.val) := by
      refine Vec.sumNat_congr (fun i => ?_)
      have h2 : Vec.sumNat (fun j : Fin 48 => Vec.sumNat (fun k : Fin 48 => AX i j * AX j k * AX k i))
          = Vec.sumNat (fun j : Fin 48 =>
              (fun b => sumN (fun c => aX i.val b * aX b c * aX c i.val) 48) j.val) := by
        refine Vec.sumNat_congr (fun j => ?_)
        have h3 : Vec.sumNat (fun k : Fin 48 => AX i j * AX j k * AX k i)
            = Vec.sumNat (fun k : Fin 48 =>
                (fun c => aX i.val j.val * aX j.val c * aX c i.val) k.val) := by
          refine Vec.sumNat_congr (fun k => ?_)
          rw [AX_eq_aX, AX_eq_aX, AX_eq_aX]
        rw [h3]
        exact sumNat_eq_sumN 48 (fun c => aX i.val j.val * aX j.val c * aX c i.val)
      rw [h2]
      exact sumNat_eq_sumN 48 (fun b => sumN (fun c => aX i.val b * aX b c * aX c i.val) 48)
    rw [h1, sumNat_eq_sumN 48
      (fun a => sumN (fun b => sumN (fun c => aX a b * aX b c * aX c a) 48) 48)]
    exact trXComp.2

/-! ## `D56`, `S32`, `S41`, `S41a`, `S41c`, `S41d`, `RC1`: the spectral layer

No real number appears. A spectrum is named by an annihilating polynomial over
`Z` (`D56`), its multiplicities are pinned by integer traces (`S32`), and the
eigenspace decomposition is carried by an exact system of orthogonal
idempotents (`S41`, `S41a`, `S41c`) rather than by a semisimplicity theorem.
`RC1` is that decomposition read as complete reducibility, and `S41d` is its
instance at the class graph. Release plan section 4.4 fixes this route:
"`RC1` discharged through `S41a` and `S41c` rather than semisimplicity".

Everything runs inside the three-dimensional algebra `Z.I + Z.A + Z.J`, which
`T7` and `T8` close: `A^2 = 24J + 4A + 32I`, `AJ = JA = 56J`, `J^2 = 120J`.
`comb a b c` is `aI + bA + cJ` and `comb_mul` is that closure. -/

public theorem nsmulInt (n : Nat) (c : Int) : nsmul n c = (n : Int) * c := by
  induction n with
  | zero => show (0 : Int) = (0 : Int) * c; omega
  | succ k ih =>
    show c + nsmul k c = ((k + 1 : Nat) : Int) * c
    rw [ih]
    have : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [this]
    grind

/-- The column sums of `A` are its row sums, because `A` is symmetric. -/
public theorem col_sum (v : K) : Vec.sum (fun k : K => Aint k v) = 56 := by
  have h : ∀ k : K, Aint k v = Aint v k := fun k => by
    show ((A k v : Nat) : Int) = ((A v k : Nat) : Int)
    rw [A_comm]
  rw [Vec.sum_congr h, deg_cast v, T7 v]
  rfl

/-- `aI + bA + cJ`, the general element of the algebra the class graph
generates. -/
@[expose] public def comb (a b c : Int) : Mat 120 120 Int :=
  fun u v => a * (if u = v then 1 else 0) + b * Aint u v + c

/-- The nine-term split of a sum, right nested: the shape `comb_mul` expands
its summand into. -/
public theorem isum9 (f1 f2 f3 f4 f5 f6 f7 f8 f9 : K → Int) :
    Vec.sum (fun k => f1 k + (f2 k + (f3 k + (f4 k + (f5 k + (f6 k
        + (f7 k + (f8 k + f9 k))))))))
      = Vec.sum f1 + (Vec.sum f2 + (Vec.sum f3 + (Vec.sum f4 + (Vec.sum f5 + (Vec.sum f6
        + (Vec.sum f7 + (Vec.sum f8 + Vec.sum f9))))))) := by
  rw [isum_add f1 (fun k => f2 k + (f3 k + (f4 k + (f5 k + (f6 k + (f7 k + (f8 k + f9 k))))))),
    isum_add f2 (fun k => f3 k + (f4 k + (f5 k + (f6 k + (f7 k + (f8 k + f9 k)))))),
    isum_add f3 (fun k => f4 k + (f5 k + (f6 k + (f7 k + (f8 k + f9 k))))),
    isum_add f4 (fun k => f5 k + (f6 k + (f7 k + (f8 k + f9 k)))),
    isum_add f5 (fun k => f6 k + (f7 k + (f8 k + f9 k))),
    isum_add f6 (fun k => f7 k + (f8 k + f9 k)),
    isum_add f7 (fun k => f8 k + f9 k),
    isum_add f8 f9]

/-- The multiplication table of `Z.I + Z.A + Z.J`. This is `T7` and `T8` in one
identity, and every idempotent fact below is arithmetic on its coefficients. -/
public theorem comb_mul (a b c a' b' c' : Int) (u v : K) :
    Mat.mul (comb a b c) (comb a' b' c') u v
      = comb (a * a' + 32 * (b * b'))
          (a * b' + b * a' + 4 * (b * b'))
          (a * c' + c * a' + 24 * (b * b') + 56 * (b * c') + 56 * (c * b')
            + 120 * (c * c')) u v := by
  have hterm : ∀ k : K, comb a b c u k * comb a' b' c' k v
      = (if u = k then a * a' * (if k = v then (1 : Int) else 0) else 0)
        + ((if u = k then a * b' * Aint k v else 0)
        + ((if u = k then a * c' else 0)
        + ((if k = v then b * a' * Aint u k else 0)
        + ((b * b') * (Aint u k * Aint k v)
        + ((b * c') * Aint u k
        + ((if k = v then c * a' else 0)
        + ((c * b') * Aint k v
        + (c * c')))))))) := by
    intro k
    show (a * (if u = k then 1 else 0) + b * Aint u k + c)
        * (a' * (if k = v then 1 else 0) + b' * Aint k v + c') = _
    by_cases h1 : u = k <;> by_cases h2 : k = v <;>
      simp only [h1, h2] <;> grind
  show Vec.sum (fun k => comb a b c u k * comb a' b' c' k v) = _
  rw [Vec.sum_congr hterm, isum9]
  rw [isum_ite u (fun k => a * a' * (if k = v then (1 : Int) else 0)),
    isum_ite u (fun k => a * b' * Aint k v),
    isum_ite u (fun _ : K => a * c'),
    isum_ite' v (fun k => b * a' * Aint u k),
    ← Blocks.isum_scale (b * b') (fun k : K => Aint u k * Aint k v),
    ← Blocks.isum_scale (b * c') (fun k : K => Aint u k),
    isum_ite' v (fun _ : K => c * a'),
    ← Blocks.isum_scale (c * b') (fun k : K => Aint k v),
    isum_const (c * c'), nsmulInt,
    deg_cast u, T7 u, col_sum v]
  show a * a' * (if u = v then (1 : Int) else 0) + (a * b' * Aint u v + (a * c'
    + (b * a' * Aint u v + ((b * b') * Mat.mul Aint Aint u v + ((b * c') * 56
    + (c * a' + ((c * b') * 56 + (120 : Int) * (c * c')))))))) = _
  rw [AA_apply u v, common_eq u v]
  show _ = (a * a' + 32 * (b * b')) * (if u = v then 1 else 0)
    + (a * b' + b * a' + 4 * (b * b')) * Aint u v
    + (a * c' + c * a' + 24 * (b * b') + 56 * (b * c') + 56 * (c * b') + 120 * (c * c'))
  have hA : Aint u v = ((A u v : Nat) : Int) := rfl
  have hcast : ((24 + 4 * A u v + (if u = v then 32 else 0) : Nat) : Int)
      = 24 + 4 * ((A u v : Nat) : Int) + (if u = v then 32 else 0) := by
    by_cases h : u = v
    · rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]; omega
  rw [hcast, hA]
  by_cases h : u = v
  · rw [if_pos h]; grind
  · rw [if_neg h]; grind


@[expose] public def isumN (f : Nat → Int) (m : Nat) : Int :=
  Nat.rec (motive := fun _ => Int) 0 (fun k ih => f k + ih) m

@[expose] public def qsumN (f : Nat → Rat) (m : Nat) : Rat :=
  Nat.rec (motive := fun _ => Rat) 0 (fun k ih => f k + ih) m

public theorem isumN_succ (f : Nat → Int) (m : Nat) : isumN f (m + 1) = f m + isumN f m := rfl

public theorem qsumN_succ (f : Nat → Rat) (m : Nat) : qsumN f (m + 1) = f m + qsumN f m := rfl

public theorem qsumN_eighth (f : Nat → Rat) (g : Nat → Int) :
    ∀ m, (∀ k, k < m → f k = (8 : Rat)⁻¹ * ((g k : Int) : Rat)) →
      qsumN f m = (8 : Rat)⁻¹ * ((isumN g m : Int) : Rat) := by
  intro m
  induction m with
  | zero =>
    intro _
    show (0 : Rat) = (8 : Rat)⁻¹ * ((0 : Int) : Rat)
    rw [Rat.intCast_zero, Rat.mul_zero]
  | succ p ih =>
    intro h
    rw [qsumN_succ, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h p (Nat.lt_succ_self p),
      isumN_succ, Rat.intCast_add]
    exact (Rat.mul_add _ _ _).symm

@[expose] public def traceZ {n : Nat} (M : Mat n n Int) : Int := Vec.sumInt (fun i => M i i)

@[expose] public def traceQ {n : Nat} (M : Mat n n Rat) : Rat := Vec.sum (fun i => M i i)

/-- An integer `8 x 8` matrix divided by `8` over `Q`. Every rational object of
this section is of this shape: `P_u` is `r_u r_u^T / 8` and `sum_{i in X} P_i`
is `M_X / 8`, so one product lemma serves both. -/
@[expose] public def scaleQ (M : Mat 8 8 Int) : Mat 8 8 Rat :=
  fun a b => (8 : Rat)⁻¹ * ((M a b : Int) : Rat)

public theorem inv8_mul : (8 : Rat)⁻¹ * ((8 : Int) : Rat) = 1 := Rat.inv_mul_cancel 8 (by decide)

public theorem mul_inv8 : ((8 : Int) : Rat) * (8 : Rat)⁻¹ = 1 := by
  rw [Rat.mul_comm]; exact inv8_mul

public theorem scaleQ_mul (M N : Mat 8 8 Int) (a c : Fin 8) :
    Mat.mul (scaleQ M) (scaleQ N) a c
      = (8 : Rat)⁻¹ * ((8 : Rat)⁻¹ * ((Mat.mul M N a c : Int) : Rat)) := by
  have hterm : ∀ b : Fin 8, mul (scaleQ M a b) (scaleQ N b c)
      = mul ((8 : Rat)⁻¹) (mul ((8 : Rat)⁻¹) (((M a b * N b c : Int) : Rat))) := by
    intro b
    show ((8 : Rat)⁻¹ * ((M a b : Int) : Rat)) * ((8 : Rat)⁻¹ * ((N b c : Int) : Rat)) = _
    rw [Rat.intCast_mul (M a b) (N b c)]
    show _ = (8 : Rat)⁻¹ * ((8 : Rat)⁻¹ * (((M a b : Int) : Rat) * ((N b c : Int) : Rat)))
    rw [← Rat.mul_assoc, ← Rat.mul_assoc,
      Rat.mul_assoc ((8:Rat)⁻¹) (((M a b : Int) : Rat)) ((8:Rat)⁻¹),
      Rat.mul_comm (((M a b : Int) : Rat)) ((8:Rat)⁻¹), ← Rat.mul_assoc, Rat.mul_assoc]
  show Vec.sum (fun b : Fin 8 => mul (scaleQ M a b) (scaleQ N b c)) = _
  rw [Vec.sum_congr hterm, ← Vec.mul_sum, ← Vec.mul_sum]
  refine congrArg (fun t => (8 : Rat)⁻¹ * ((8 : Rat)⁻¹ * t)) ?_
  rw [Mat.mul_apply]
  exact (hom_map_sum intToRat (fun b : Fin 8 => mul (M a b) (N b c))).symm

public theorem traceQ_scaleQ (M : Mat 8 8 Int) :
    traceQ (scaleQ M) = (8 : Rat)⁻¹ * ((traceZ M : Int) : Rat) := by
  show Vec.sum (fun a : Fin 8 => mul ((8 : Rat)⁻¹) (((M a a : Int) : Rat)))
      = mul ((8 : Rat)⁻¹) (((traceZ M : Int) : Rat))
  rw [← Vec.mul_sum]
  refine congrArg (fun t => mul ((8 : Rat)⁻¹) t) ?_
  show _ = ((Vec.sumInt (fun a : Fin 8 => M a a) : Int) : Rat)
  rw [Vec.sumInt_eq_sum]
  exact (hom_map_sum intToRat (fun a : Fin 8 => M a a)).symm


/-- `r r^T`, the rank-one integer matrix behind `P_u`. -/
@[expose] public def outer (x : Vec 8 Int) : Mat 8 8 Int := fun a b => x a * x b

public theorem outer_mul (x y : Vec 8 Int) (a c : Fin 8) :
    Mat.mul (outer x) (outer y) a c = x a * y c * dot x y := by
  have hterm : ∀ b : Fin 8, mul (outer x a b) (outer y b c) = mul (x a * y c) (x b * y b) := by
    intro b
    show x a * x b * (y b * y c) = x a * y c * (x b * y b)
    have h1 := Int.mul_comm (x b) (y c)
    grind
  have hdot : dot x y = Vec.sum (fun b : Fin 8 => x b * y b) :=
    Vec.sumInt_eq_sum (fun b : Fin 8 => x b * y b)
  show Vec.sum (fun b : Fin 8 => mul (outer x a b) (outer y b c)) = _
  rw [Vec.sum_congr hterm, ← Vec.mul_sum, hdot]
  rfl

public theorem traceZ_outer (x : Vec 8 Int) : traceZ (outer x) = dot x x := rfl

/-- `P_u`, the orthogonal projection on the line of the class `u`, over `Q`. -/
@[expose] public def projQ (u : K) : Mat 8 8 Rat := scaleQ (outer (rep u))

public theorem inv8_cancel (x : Rat) : (8 : Rat)⁻¹ * (((8 : Int) : Rat) * x) = x := by
  rw [← Rat.mul_assoc, inv8_mul, Rat.one_mul]

public theorem inv8_cancel' (x : Rat) : ((8 : Int) : Rat) * ((8 : Rat)⁻¹ * x) = x := by
  rw [← Rat.mul_assoc, Rat.mul_comm (((8 : Int) : Rat)) ((8 : Rat)⁻¹), inv8_mul, Rat.one_mul]

/-- Each `P_u` is idempotent: `P_u^2 = P_u`.

This is NOT the document's `S33`, which is `A_X = 4(M_X - I)` with
`M_X = [tr(P_i P_j)]` and the nonzero spectrum of `M_X` equal to that of `S_X`.
A true theorem under a label whose statement is something else is exactly what
the register exists to prevent, so it is named for what it proves. `S33` itself
is proved below, in the section on the frame operator. -/
public theorem projQ_idem (u : K) (a c : Fin 8) : Mat.mul (projQ u) (projQ u) a c = projQ u a c := by
  rw [projQ, scaleQ_mul, outer_mul, (D11_rep u).2]
  show (8 : Rat)⁻¹ * ((8 : Rat)⁻¹ * ((rep u a * rep u c * 8 : Int) : Rat))
    = (8 : Rat)⁻¹ * ((rep u a * rep u c : Int) : Rat)
  rw [Rat.intCast_mul (rep u a * rep u c) 8]
  refine congrArg (fun t => (8 : Rat)⁻¹ * t) ?_
  rw [Rat.mul_comm (((rep u a * rep u c : Int)) : Rat) (((8 : Int) : Rat))]
  exact inv8_cancel _

/-- Each `P_u` is symmetric of trace `1`: a rank-one projection.

NOT the document's `S34`, which is `S_amb = 3.Id + (3/2)tr(.)I` --- the
statement that the ambient roots form a spherical `4`-design. `S34` itself is
proved below, off the fourth moment tensor `mom4_amb`. -/
public theorem projQ_symm_trace (u : K) :
    (∀ a b : Fin 8, projQ u a b = projQ u b a) ∧ traceQ (projQ u) = 1 := by
  refine ⟨fun a b => ?_, ?_⟩
  · show (8 : Rat)⁻¹ * ((rep u a * rep u b : Int) : Rat)
      = (8 : Rat)⁻¹ * ((rep u b * rep u a : Int) : Rat)
    rw [Int.mul_comm (rep u a) (rep u b)]
  · rw [projQ, traceQ_scaleQ, traceZ_outer, (D11_rep u).2]
    exact inv8_mul

/-- The trace form on the projections is the squared inner product of the
representatives: `4 tr(P_u P_v) = <r_u,r_v>^2` in the normalisation where a root
has norm `2`, which in the `2x` scaling of this library reads
`64 tr(P_u P_v) = <rep_u,rep_v>^2`.

NOT the document's `S35`, which is the operator identity
`S_res = S_amb - S_atlas`, resting on the additivity of `X |-> S_X`. `S35`
itself is proved below. -/
public theorem projQ_trace_dot (u v : K) :
    (64 : Rat) * traceQ (Mat.mul (projQ u) (projQ v))
      = ((dot (rep u) (rep v) * dot (rep u) (rep v) : Int) : Rat) := by
  have hentry : ∀ a : Fin 8, Mat.mul (projQ u) (projQ v) a a
      = mul ((8 : Rat)⁻¹ * (8 : Rat)⁻¹)
          (((rep u a * rep v a * dot (rep u) (rep v) : Int) : Rat)) := by
    intro a
    rw [projQ, projQ, scaleQ_mul, outer_mul]
    show (8 : Rat)⁻¹ * ((8 : Rat)⁻¹ * _) = ((8 : Rat)⁻¹ * (8 : Rat)⁻¹) * _
    rw [Rat.mul_assoc]
  have hcast : Vec.sum (fun a : Fin 8 =>
      ((rep u a * rep v a * dot (rep u) (rep v) : Int) : Rat))
      = ((Vec.sum (fun a : Fin 8 => rep u a * rep v a * dot (rep u) (rep v)) : Int) : Rat) :=
    (hom_map_sum intToRat (fun a : Fin 8 => rep u a * rep v a * dot (rep u) (rep v))).symm
  have hint : Vec.sum (fun a : Fin 8 => rep u a * rep v a * dot (rep u) (rep v))
      = dot (rep u) (rep v) * dot (rep u) (rep v) := by
    show Vec.sum (fun a : Fin 8 => mul (rep u a * rep v a) (dot (rep u) (rep v))) = _
    rw [← Vec.sum_mul]
    exact congrArg (fun t : Int => t * dot (rep u) (rep v))
      (Vec.sumInt_eq_sum (fun a : Fin 8 => rep u a * rep v a)).symm
  have hkey : traceQ (Mat.mul (projQ u) (projQ v))
      = ((8 : Rat)⁻¹ * (8 : Rat)⁻¹)
        * ((dot (rep u) (rep v) * dot (rep u) (rep v) : Int) : Rat) := by
    show Vec.sum (fun a : Fin 8 => Mat.mul (projQ u) (projQ v) a a) = _
    rw [Vec.sum_congr hentry, ← Vec.mul_sum, hcast, hint]
    rfl
  rw [hkey]
  have h64 : (64 : Rat) = ((8 : Int) : Rat) * ((8 : Int) : Rat) := by decide +kernel
  rw [h64, Rat.mul_assoc, ← Rat.mul_assoc (((8 : Int) : Rat)) ((8 : Rat)⁻¹ * (8 : Rat)⁻¹) _]
  rw [← Rat.mul_assoc (((8 : Int) : Rat)) ((8 : Rat)⁻¹) ((8 : Rat)⁻¹),
    Rat.mul_comm (((8 : Int) : Rat)) ((8 : Rat)⁻¹), inv8_mul, Rat.one_mul]
  exact inv8_cancel' _


public theorem outer_nrm (x : Vec 8 Int) : outer (nrm x) = outer x := by
  by_cases h : 0 < dot x posRef
  · rw [show nrm x = x from if_pos h]
  · rw [show nrm x = neg x from if_neg h]
    funext a b
    show neg x a * neg x b = x a * x b
    show -(x a) * -(x b) = x a * x b
    grind

/-- The projection depends on the class, not on the representative: the two
roots `+-x` of a class give the same `P`.

NOT the document's `S36`, which derives the residue spectrum from the
AtlasInstance spectrum by `lambda |-> 3 - lambda` on the traceless part. `S36`
itself is proved below, out of `S34` and `S35`. -/
public theorem projQ_of_root (x : Vec 8 Int) (h : D11 x) : scaleQ (outer x) = projQ (D12 x) := by
  rw [projQ, rep_D12 h, outer_nrm]

/-- Orthogonal classes have orthogonal projections, and adjacent ones meet the
trace form in `1/4`.

This is one geometric input to `S37` below. The label itself combines the
affine eigenspace correspondence with the exact multiplicity ledger and the
split rank certificate, rather than being attached to this local identity. -/
public theorem projQ_orth (u v : K) :
    (D52 u v → ∀ a c : Fin 8, Mat.mul (projQ u) (projQ v) a c = 0)
      ∧ (D13 u v → (64 : Rat) * traceQ (Mat.mul (projQ u) (projQ v)) = 16) := by
  refine ⟨fun ho a c => ?_, fun hd => ?_⟩
  · rw [projQ, projQ, scaleQ_mul, outer_mul, ho.2]
    show (8 : Rat)⁻¹ * ((8 : Rat)⁻¹ * ((rep u a * rep v c * 0 : Int) : Rat)) = 0
    rw [Int.mul_zero, Rat.intCast_zero, Rat.mul_zero, Rat.mul_zero]
  · rw [projQ_trace_dot u v]
    rcases hd.2 with hh | hh <;> rw [hh] <;> decide +kernel

/-- The squared inner product of two representatives, in closed form: `0` on
orthogonal classes, `16` on adjacent ones, `64` on the diagonal. This is
`dotTri` read as an identity rather than as a trichotomy, and it is what makes
`ProjGram` equal `4I + A`. -/
public theorem dot_rep_sq (u v : K) :
    dot (rep u) (rep v) * dot (rep u) (rep v)
      = 16 * (4 * (if u = v then 1 else 0) + ((A u v : Nat) : Int)) := by
  by_cases h : u = v
  · subst h
    rw [if_pos rfl, A_diag u, (D11_rep u).2]
    decide
  · rw [if_neg h]
    have htri := allLt_true _ _ (allLt_true _ _ dotTri u.val u.isLt) v.val v.isLt
    rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at htri
    have hne : ¬ (u.val = v.val) := fun he => h (Fin.eq_of_val_eq he)
    have hd : dot (rep u) (rep v) = 0 ∨ dot (rep u) (rep v) = 4
        ∨ dot (rep u) (rep v) = -4 := by
      rcases htri with ((h1 | h1) | h1) | h1
      · exact absurd (of_decide_eq_true h1) hne
      · exact Or.inl (of_decide_eq_true h1)
      · exact Or.inr (Or.inl (of_decide_eq_true h1))
      · exact Or.inr (Or.inr (of_decide_eq_true h1))
    rcases hd with hh | hh | hh
    · have hnd : ¬ D13 u v := by
        intro hdd
        rcases hdd.2 with h2 | h2 <;> rw [hh] at h2 <;> exact absurd h2 (by decide)
      rw [hh, A_of_not_D13 hnd]
      decide
    · rw [hh, A_of_D13 ⟨h, Or.inl hh⟩]; decide
    · rw [hh, A_of_D13 ⟨h, Or.inr hh⟩]; decide

/-- `D55`. `ProjGram(X)[i][j] := <r_i,r_j>^2`, the Gram matrix of the
projections in the trace form: `projQ_trace_dot` reads it as `4 tr(P_i P_j)`. In the `2x`
scaling of this library `<rep_i,rep_j> = 4 <r_i,r_j>`, so the entry is
`<rep_i,rep_j>^2 / 16`, and `dot_rep_sq` makes that division exact. -/
@[expose] public def D55 {m : Nat} (x : Fin m → K) : Mat m m Int :=
  fun i j => dot (rep (x i)) (rep (x j)) * dot (rep (x i)) (rep (x j)) / 16

public theorem D55_exact {m : Nat} (x : Fin m → K) (i j : Fin m) :
    16 * D55 x i j = dot (rep (x i)) (rep (x j)) * dot (rep (x i)) (rep (x j)) := by
  show 16 * (dot (rep (x i)) (rep (x j)) * dot (rep (x i)) (rep (x j)) / 16) = _
  rw [dot_rep_sq (x i) (x j), Int.mul_ediv_cancel_left _ (by decide : (16 : Int) ≠ 0)]

/-- `ProjGram(X) = 4I + A_X`, for any injective listing of a class set. -/
public theorem D55_eq {m : Nat} (x : Fin m → K) (hinj : ∀ i j : Fin m, x i = x j → i = j)
    (i j : Fin m) : D55 x i j = 4 * (if i = j then 1 else 0) + ((A (x i) (x j) : Nat) : Int) := by
  have h16 : 16 * D55 x i j
      = 16 * (4 * (if i = j then 1 else 0) + ((A (x i) (x j) : Nat) : Int)) := by
    rw [D55_exact, dot_rep_sq]
    by_cases h : i = j
    · rw [if_pos h, if_pos (congrArg x h)]
    · rw [if_neg h, if_neg (fun he => h (hinj i j he))]
  omega


/-- The trace form on integer `8 x 8` matrices, `<M,N> = tr(M N^T)`. It is the
form `S13` exhibits `ProjGram` as a Gram matrix in, and it is a sum of squares
on the diagonal, which is the whole of the positive-semidefiniteness. -/
@[expose] public def tform (M N : Mat 8 8 Int) : Int :=
  Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 => M a b * N a b))

/-- Exchanging a sum over classes with the double sum over coordinates. -/
public theorem exch2 {m : Nat} (F : Fin m → Fin 8 → Fin 8 → Int) :
    Vec.sum (fun i : Fin m => Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 => F i a b)))
      = Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 =>
          Vec.sum (fun i : Fin m => F i a b))) := by
  rw [Vec.sum_exchange (fun (i : Fin m) (a : Fin 8) => Vec.sum (fun b : Fin 8 => F i a b))]
  exact Vec.sum_congr (fun a => Vec.sum_exchange (fun (i : Fin m) (b : Fin 8) => F i a b))

public theorem outer_pair (y z : Vec 8 Int) (k : Int) :
    Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 => (y a * y b) * (k * (z a * z b))))
      = k * (dot y z * dot y z) := by
  have hdot : dot y z = Vec.sum (fun b : Fin 8 => y b * z b) :=
    Vec.sumInt_eq_sum (fun b : Fin 8 => y b * z b)
  have hin : ∀ a : Fin 8, Vec.sum (fun b : Fin 8 => (y a * y b) * (k * (z a * z b)))
      = mul (k * (y a * z a)) (dot y z) := by
    intro a
    have hb : ∀ b : Fin 8, (y a * y b) * (k * (z a * z b))
        = mul (k * (y a * z a)) (y b * z b) := by
      intro b
      show (y a * y b) * (k * (z a * z b)) = (k * (y a * z a)) * (y b * z b)
      grind
    rw [Vec.sum_congr hb, ← Vec.mul_sum, hdot]
  rw [Vec.sum_congr hin]
  have ha : ∀ a : Fin 8, mul (k * (y a * z a)) (dot y z)
      = mul (k * dot y z) (y a * z a) := by
    intro a
    show (k * (y a * z a)) * dot y z = (k * dot y z) * (y a * z a)
    grind
  rw [Vec.sum_congr ha, ← Vec.mul_sum, ← hdot]
  exact Int.mul_assoc k (dot y z) (dot y z)

/-- `sum_i c_i r_i r_i^T`: the vector of the Gram factorisation, at the
coefficients `c`. -/
@[expose] public def gramComb {m : Nat} (x : Fin m → K) (c : Vec m Int) : Mat 8 8 Int :=
  fun a b => Vec.sum (fun i : Fin m => c i * (rep (x i) a * rep (x i) b))

public theorem tform_outer_left {m : Nat} (x : Fin m → K) (c : Vec m Int) (i : Fin m) :
    tform (outer (rep (x i))) (gramComb x c)
      = Vec.sum (fun j : Fin m => c j *
          (dot (rep (x i)) (rep (x j)) * dot (rep (x i)) (rep (x j)))) := by
  have hexp : ∀ a b : Fin 8,
      (outer (rep (x i)) a b) * (gramComb x c a b)
        = Vec.sum (fun j : Fin m =>
            (rep (x i) a * rep (x i) b) * (c j * (rep (x j) a * rep (x j) b))) := by
    intro a b
    exact Vec.mul_sum (rep (x i) a * rep (x i) b)
      (fun j : Fin m => c j * (rep (x j) a * rep (x j) b))
  show Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 =>
      (outer (rep (x i)) a b) * (gramComb x c a b))) = _
  rw [Vec.sum_congr (fun a => Vec.sum_congr (fun b => hexp a b)),
    ← exch2 (fun (j : Fin m) (a : Fin 8) (b : Fin 8) =>
      (rep (x i) a * rep (x i) b) * (c j * (rep (x j) a * rep (x j) b)))]
  exact Vec.sum_congr (fun j => outer_pair (rep (x i)) (rep (x j)) (c j))

public theorem tform_comb {m : Nat} (x : Fin m → K) (c : Vec m Int) :
    Vec.sum (fun i : Fin m => c i * tform (outer (rep (x i))) (gramComb x c))
      = tform (gramComb x c) (gramComb x c) := by
  have hexp : ∀ i : Fin m, c i * tform (outer (rep (x i))) (gramComb x c)
      = Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 =>
          c i * ((rep (x i) a * rep (x i) b) * gramComb x c a b))) := by
    intro i
    have h1 : mul (c i) (Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 =>
        mul (outer (rep (x i)) a b) (gramComb x c a b))))
        = Vec.sum (fun a : Fin 8 => mul (c i) (Vec.sum (fun b : Fin 8 =>
          mul (outer (rep (x i)) a b) (gramComb x c a b)))) :=
      Vec.mul_sum (c i) _
    refine Eq.trans h1 (Vec.sum_congr (fun a => ?_))
    exact Vec.mul_sum (c i) (fun b : Fin 8 =>
      mul (outer (rep (x i)) a b) (gramComb x c a b))
  rw [Vec.sum_congr hexp, exch2 (fun (i : Fin m) (a : Fin 8) (b : Fin 8) =>
      c i * ((rep (x i) a * rep (x i) b) * gramComb x c a b))]
  refine Vec.sum_congr (fun a => Vec.sum_congr (fun b => ?_))
  have hb : ∀ i : Fin m, c i * ((rep (x i) a * rep (x i) b) * gramComb x c a b)
      = mul (c i * (rep (x i) a * rep (x i) b)) (gramComb x c a b) := by
    intro i
    show _ = (c i * (rep (x i) a * rep (x i) b)) * gramComb x c a b
    grind
  rw [Vec.sum_congr hb, ← Vec.sum_mul]
  rfl

/-- `S13`. `ProjGram(X) = 4I + A_X` is exhibited **as** a Gram matrix: its
`(i,j)` entry is the trace form of the explicit integer matrices
`r_i r_i^T` and `r_j r_j^T`. Consequently the quadratic form it carries is a
sum of squares at every integer coefficient vector and every class set, which
is exactly the bound `lambda_min(A_X) >= -4` at every scale, stated without
leaving `Z`. -/
public theorem S13 {m : Nat} (x : Fin m → K) (c : Vec m Int) :
    (∀ i j : Fin m, 16 * D55 x i j = tform (outer (rep (x i))) (outer (rep (x j))))
      ∧ 16 * Vec.sum (fun i : Fin m => Vec.sum (fun j : Fin m => c i * (c j * D55 x i j)))
          = tform (gramComb x c) (gramComb x c)
      ∧ 0 ≤ Vec.sum (fun i : Fin m => Vec.sum (fun j : Fin m => c i * (c j * D55 x i j))) := by
  have hgram : ∀ i j : Fin m,
      16 * D55 x i j = tform (outer (rep (x i))) (outer (rep (x j))) := by
    intro i j
    have h := outer_pair (rep (x i)) (rep (x j)) 1
    show _ = Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 =>
      (outer (rep (x i)) a b) * (outer (rep (x j)) a b)))
    have hc : ∀ a b : Fin 8, (outer (rep (x i)) a b) * (outer (rep (x j)) a b)
        = (rep (x i) a * rep (x i) b) * (1 * (rep (x j) a * rep (x j) b)) := by
      intro a b
      show (rep (x i) a * rep (x i) b) * (rep (x j) a * rep (x j) b)
          = (rep (x i) a * rep (x i) b) * (1 * (rep (x j) a * rep (x j) b))
      rw [Int.one_mul]
    rw [Vec.sum_congr (fun a => Vec.sum_congr (fun b => hc a b)), h, D55_exact, Int.one_mul]
  have hsq : 16 * Vec.sum (fun i : Fin m => Vec.sum (fun j : Fin m => c i * (c j * D55 x i j)))
      = tform (gramComb x c) (gramComb x c) := by
    have hi : ∀ i : Fin m, c i * tform (outer (rep (x i))) (gramComb x c)
        = 16 * Vec.sum (fun j : Fin m => c i * (c j * D55 x i j)) := by
      intro i
      have hj : ∀ j : Fin m,
          c j * (dot (rep (x i)) (rep (x j)) * dot (rep (x i)) (rep (x j)))
            = mul 16 (c j * D55 x i j) := by
        intro j
        rw [← D55_exact x i j]
        show c j * (16 * D55 x i j) = 16 * (c j * D55 x i j)
        rw [← Int.mul_assoc, Int.mul_comm (c j) 16, Int.mul_assoc]
      have hr : Vec.sum (fun j : Fin m => c i * (c j * D55 x i j))
          = mul (c i) (Vec.sum (fun j : Fin m => c j * D55 x i j)) :=
        (Vec.mul_sum (c i) (fun j : Fin m => c j * D55 x i j)).symm
      rw [tform_outer_left x c i, Vec.sum_congr hj, ← Vec.mul_sum, hr]
      show c i * (16 * Vec.sum (fun j : Fin m => c j * D55 x i j))
        = 16 * (c i * Vec.sum (fun j : Fin m => c j * D55 x i j))
      rw [← Int.mul_assoc, Int.mul_comm (c i) 16, Int.mul_assoc]
    rw [← tform_comb x c, Vec.sum_congr hi]
    exact Vec.mul_sum 16 (fun i : Fin m =>
      Vec.sum (fun j : Fin m => c i * (c j * D55 x i j)))
  refine ⟨hgram, hsq, ?_⟩
  have hnn : 0 ≤ tform (gramComb x c) (gramComb x c) := by
    show 0 ≤ Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 =>
      gramComb x c a b * gramComb x c a b))
    rw [← Vec.sumInt_eq_sum]
    refine sumInt_nonneg _ (fun a => ?_)
    rw [← Vec.sumInt_eq_sum]
    exact sumInt_nonneg _ (fun b => mul_self_nonneg _)
  omega


public theorem qmul_left_comm (p q z : Rat) : p * (q * z) = q * (p * z) := by
  rw [← Rat.mul_assoc, Rat.mul_comm p q, Rat.mul_assoc]

public theorem inv8_pull (w z : Rat) :
    w * ((8 : Rat)⁻¹ * ((8 : Rat)⁻¹ * z)) = (8 : Rat)⁻¹ * ((8 : Rat)⁻¹ * (w * z)) := by
  rw [qmul_left_comm w ((8 : Rat)⁻¹) ((8 : Rat)⁻¹ * z)]
  exact congrArg (fun t => (8 : Rat)⁻¹ * t) (qmul_left_comm w ((8 : Rat)⁻¹) z)

/-- `M_X := sum_{i in X} r_i r_i^T` over `Z`. Since `P_i = r_i r_i^T / 8`, this
is `8 sum_{i in X} P_i`, and `projSum_eq` says exactly that. -/
@[expose] public def frameSum (W : Bitset) : Mat 8 8 Int :=
  fun a b => isumN (fun u => if u ∈ W then repN u a * repN u b else 0) 120

@[expose] public def kOf (u : Nat) : K := ⟨u % 120, Nat.mod_lt _ (by decide)⟩

/-- `sum_{i in X} P_i`, the frame operator of the class set `X` on `Q^8`. -/
@[expose] public def projSum (W : Bitset) : Mat 8 8 Rat :=
  fun a b => qsumN (fun u => if u ∈ W then projQ (kOf u) a b else 0) 120

public theorem projSum_eq (W : Bitset) : projSum W = scaleQ (frameSum W) := by
  funext a b
  refine qsumN_eighth _ _ 120 (fun k hk => ?_)
  have hrep : rep (kOf k) = repN k := by
    show repN ((kOf k).val) = repN k
    exact congrArg repN (Nat.mod_eq_of_lt hk)
  by_cases h : k ∈ W
  · rw [if_pos h, if_pos h]
    show (8 : Rat)⁻¹ * ((rep (kOf k) a * rep (kOf k) b : Int) : Rat) = _
    rw [hrep]
  · rw [if_neg h, if_neg h, Rat.intCast_zero, Rat.mul_zero]

/-- `D57`. `two_design_exact(X, m, r)`, decided over `Q`: the `m` lines of `X`
form a spherical `2`-design **relative to their own span**. Exactly: the frame
operator `S = sum_{i in X} P_i` satisfies `r S^2 = m S` and `tr S = r`, so
`(r/m) S` is an idempotent of trace `r` -- the orthogonal projection on an
`r`-dimensional subspace, which is `span(X)` because `S` is supported there.
Nothing here leaves `Q`. -/
@[expose] public def D57 (W : Bitset) (m r : Int) : Prop :=
  (∀ a b : Fin 8, ((r : Int) : Rat) * (Mat.mul (projSum W) (projSum W) a b)
      = ((m : Int) : Rat) * (projSum W a b))
    ∧ traceQ (projSum W) = ((m : Int) : Rat)

public theorem D57_of_int {W : Bitset} {m r C : Int}
    (hsq : ∀ a b : Fin 8, Mat.mul (frameSum W) (frameSum W) a b = C * frameSum W a b)
    (hC : r * C = 8 * m)
    (htr : traceZ (frameSum W) = 8 * m) : D57 W m r := by
  constructor
  · intro a b
    rw [projSum_eq, scaleQ_mul, hsq a b]
    show ((r : Int) : Rat) * ((8 : Rat)⁻¹ * ((8 : Rat)⁻¹ * ((C * frameSum W a b : Int) : Rat)))
      = ((m : Int) : Rat) * ((8 : Rat)⁻¹ * ((frameSum W a b : Int) : Rat))
    rw [inv8_pull, Rat.intCast_mul C (frameSum W a b),
      ← Rat.mul_assoc (((r : Int) : Rat)) (((C : Int) : Rat)) _,
      ← Rat.intCast_mul r C, hC, Rat.intCast_mul 8 m,
      Rat.mul_assoc (((8 : Int) : Rat)) (((m : Int) : Rat)) _,
      qmul_left_comm ((8 : Rat)⁻¹) ((8 : Rat)⁻¹) _, ← Rat.mul_assoc ((8 : Rat)⁻¹) (((8:Int):Rat)) _,
      Rat.mul_comm ((8 : Rat)⁻¹) (((8 : Int) : Rat)), mul_inv8, Rat.one_mul]
    exact (qmul_left_comm (((m : Int) : Rat)) ((8 : Rat)⁻¹) _).symm
  · rw [projSum_eq, traceQ_scaleQ, htr, Rat.intCast_mul 8 m, ← Rat.mul_assoc,
      inv8_mul, Rat.one_mul]


@[expose] public def towerSet : Fin 5 → Bitset := fun s =>
  if s.val = 0 then fullK
  else if s.val = 1 then residue atlSet
  else if s.val = 2 then atlSet
  else if s.val = 3 then Bitset.union (blkSet 0) (blkSet 3)
  else blkSet 0

@[expose] public def towerCard : Fin 5 → Int := fun s =>
  if s.val = 0 then 120 else if s.val = 1 then 72 else if s.val = 2 then 48
  else if s.val = 3 then 24 else 12

@[expose] public def towerRank : Fin 5 → Int := fun s => if s.val = 4 then 4 else 8

@[expose] public def towerC : Fin 5 → Int := fun s =>
  if s.val = 0 then 120 else if s.val = 1 then 72 else if s.val = 2 then 48 else 24

public theorem towerArith : ∀ s : Fin 5, towerRank s * towerC s = 8 * towerCard s := by decide

public theorem towerDesignComp :
    allFin (fun s : Fin 5 => allFin (fun a : Fin 8 => allFin (fun b : Fin 8 =>
      decide (Mat.mul (frameSum (towerSet s)) (frameSum (towerSet s)) a b
        = towerC s * frameSum (towerSet s) a b)))) = true := by decide +kernel

public theorem towerTraceComp :
    allFin (fun s : Fin 5 => decide (traceZ (frameSum (towerSet s)) = 8 * towerCard s))
      = true := by decide +kernel

public theorem towerDiagComp :
    allFin (fun s : Fin 5 => !decide (s.val < 4) || allFin (fun a : Fin 8 => allFin
      (fun b : Fin 8 => decide (frameSum (towerSet s) a b = if a = b then towerC s else 0))))
      = true := by decide +kernel

public theorem towerBlockOff : frameSum (towerSet 4) 7 7 = 0 := by decide +kernel

/-- `S17`. -/
public theorem S17 :
    (∀ s : Fin 5, D57 (towerSet s) (towerCard s) (towerRank s))
      ∧ (∀ s : Fin 5, s.val < 4 → ∀ a b : Fin 8,
          frameSum (towerSet s) a b = if a = b then towerC s else 0)
      ∧ (∃ a : Fin 8, frameSum (towerSet 4) a a = 0) := by
  refine ⟨fun s => D57_of_int (fun a b => of_decide_eq_true
      (allFin_true _ (allFin_true _ (allFin_true _ towerDesignComp s) a) b))
      (towerArith s) (of_decide_eq_true (allFin_true _ towerTraceComp s)),
    fun s hs a b => ?_, ⟨7, towerBlockOff⟩⟩
  have h := allFin_true _ towerDiagComp s
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h1 | h1
  · exact absurd (decide_eq_true hs) (by rw [h1]; exact fun hh => absurd hh (by decide))
  · exact of_decide_eq_true (allFin_true _ (allFin_true _ h1 a) b)

public theorem frameSumComp :
    allFin (fun t : Fin 15 => allFin (fun a : Fin 8 => allFin (fun b : Fin 8 =>
      decide (frameSum (frameAt kFrameTable t.val) a b = if a = b then 8 else 0)))) = true := by
  decide +kernel

/-- An OrthFrame is an orthogonal basis: the eight projections of a frame sum
to the identity, `sum_{i in F} P_i = I`.

This is the identity input to `S38` below, where the top eigenvalue is bounded
at both the AtlasInstance and its residue and the two zero multiplicities are
matched to the codimensions of `S15`. -/
public theorem orthFrame_projSum_id (t : Fin 15) (a b : Fin 8) :
    projSum (frameAt kFrameTable t.val) a b = (Mat.id : Mat 8 8 Rat) a b := by
  have h : frameSum (frameAt kFrameTable t.val) a b = if a = b then 8 else 0 :=
    of_decide_eq_true (allFin_true _ (allFin_true _ (allFin_true _ frameSumComp t) a) b)
  rw [projSum_eq]
  show (8 : Rat)⁻¹ * ((frameSum (frameAt kFrameTable t.val) a b : Int) : Rat)
    = (if a = b then (1 : Rat) else 0)
  rw [h]
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab]; exact inv8_mul
  · rw [if_neg hab, if_neg hab, Rat.intCast_zero, Rat.mul_zero]


/-- The degree of the class graph induced on each tower scale. -/
@[expose] public def towerDeg : Fin 5 → Nat := fun s =>
  if s.val = 0 then 56 else if s.val = 1 then 32 else if s.val = 2 then 20 else 8

public theorem D14_fullK (v : K) : D14 fullK v = deg v := by
  have h : ∀ u : K, (if u.val ∈ fullK then A u v else 0) = A v u := by
    intro u
    rw [if_pos ((mem_fullK u.val).mpr u.isLt), A_comm]
  show Vec.sumNat (fun u : K => if u.val ∈ fullK then A u v else 0) = deg v
  exact Vec.sumNat_congr h

/-- Regularity of a class subset as one `Bool`, run only on its own members. -/
@[expose] public def regOK (W : Bitset) (d : Nat) : Bool :=
  allLt (fun v => !Bitset.mem W v || decide (degN W v = d)) 120

public theorem reg_of_regOK {W : Bitset} {d : Nat} (h : regOK W d = true)
    (v : K) (hv : v.val ∈ W) : D14 W v = d := by
  have h1 := allLt_true _ _ h v.val v.isLt
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h1
  have hm : Bitset.mem W v.val = true := hv
  rcases h1 with h2 | h2
  · rw [h2] at hm; exact absurd hm (by decide)
  · rw [D14_eq_degN]
    exact of_decide_eq_true h2

public theorem regLowComp :
    regOK (Bitset.union (blkSet 0) (blkSet 3)) 8 = true ∧ regOK (blkSet 0) 8 = true := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- `S16`. -/
public theorem S16 (s : Fin 5) (v : K) (hv : v.val ∈ towerSet s) :
    D14 (towerSet s) v = towerDeg s := by
  match s with
  | ⟨0, _⟩ => rw [show towerSet ⟨0, by omega⟩ = fullK from rfl, D14_fullK v]; exact T7 v
  | ⟨1, _⟩ => exact (S22.2.1 v hv).1
  | ⟨2, _⟩ => exact (S22.1 v hv).1
  | ⟨3, _⟩ => exact reg_of_regOK regLowComp.1 v hv
  | ⟨4, _⟩ => exact reg_of_regOK regLowComp.2 v hv


/-! ## `D53`: containment-orthogonality -/

public structure D53 (S : Bitset) (k n r : Nat) where
  part : Nat → Bitset
  isFrame : ∀ a, a < k → D54 S (part a) n
  disjoint : ∀ a b, a < k → b < k → a ≠ b → Bitset.inter (part a) (part b) = Bitset.empty
  basis : Fin r → Vec 8 Int
  basis_mem : ∀ i : Fin r, (D12 (basis i)).val ∈ unionUpto part k
  indep : Indep basis
  spans : ∀ v : K, v.val ∈ S → InSpan basis (qOf (rep v))

@[expose] public def d53Tab : Nat := 3978416988284911872

@[expose] public def d53Basis : Fin 8 → Vec 8 Int := fun i => repN (byteAt d53Tab i.val)

public theorem d53Comp :
    allFin (fun i : Fin 8 => allFin (fun j : Fin 8 =>
        decide (dot (d53Basis i) (d53Basis j) = if i = j then 8 else 0))) = true := by
  decide +kernel

public theorem d53Mem :
    allFin (fun i : Fin 8 => Bitset.mem (frameAt kFrameTable 0) (byteAt d53Tab i.val)) = true := by
  decide +kernel

public theorem d53Recon :
    allLt (fun c => allFin (fun j : Fin 8 =>
      decide (8 * repN c j = Vec.sumInt (fun i : Fin 8 =>
        dot (repN c) (d53Basis i) * d53Basis i j)))) 120 = true := by
  decide +kernel


public theorem d53Lt :
    allFin (fun i : Fin 8 => decide (byteAt d53Tab i.val < 120)) = true := by decide

/-- The witness. -/
@[expose] public def d53Witness : D53 fullK 1 8 8 where
  part := frameAt kFrameTable
  isFrame := fun a ha =>
    (partition_of_partOK kFrameComp).isFrame a (Nat.lt_of_lt_of_le ha (by omega))
  disjoint := fun a b ha hb hab => absurd (by omega : a = b) hab
  basis := d53Basis
  basis_mem := by
    intro i
    refine (mem_unionUpto _ _ 1).mpr ⟨0, by omega, ?_⟩
    have hlt : byteAt d53Tab i.val < 120 := of_decide_eq_true (allFin_true _ d53Lt i)
    have h : (D12 (d53Basis i)).val = byteAt d53Tab i.val := D12_repN hlt
    rw [h]
    exact allFin_true _ d53Mem i
  indep := indep_of_orth d53Basis (fun i j => of_decide_eq_true
    (allFin_true _ (allFin_true _ d53Comp i) j))
  spans := by
    intro v _
    exact inSpan_of_recon d53Basis (rep v) (fun j =>
      of_decide_eq_true (allFin_true _ (allLt_true _ _ d53Recon v.val v.isLt) j))

public theorem d53NotCover : unionUpto (frameAt kFrameTable) 1 ≠ fullK := by decide +kernel


@[expose] public def blkToAtl (a t : Nat) : Nat := if a = 0 then t else if a = 3 then t else t + 3

public theorem S10Comp : allFin (fun a : Fin 4 => allLt (fun t =>
    allFin (fun s : Fin 6 =>
      decide (Bitset.subset (blkFrame a.val t) (frameAt atlFrameTable s.val)
        = decide (s.val = blkToAtl a.val t)))) 3) = true := by decide +kernel

public theorem blkToAtl_lt (a t : Nat) (_ha : a < 4) (ht : t < 3) : blkToAtl a t < 6 := by
  unfold blkToAtl
  by_cases h0 : a = 0
  · rw [if_pos h0]; omega
  · rw [if_neg h0]
    by_cases h3 : a = 3
    · rw [if_pos h3]; omega
    · rw [if_neg h3]; omega

/-- `S10`. -/
public theorem S10 (a : Fin 4) (t : Nat) (ht : t < 3) :
    ∃ s : Fin 6, Bitset.subset ((blkPart a).part t) (frameAt atlFrameTable s.val) = true
      ∧ ∀ s' : Fin 6, Bitset.subset ((blkPart a).part t) (frameAt atlFrameTable s'.val) = true
          → s' = s := by
  have key : ∀ s : Fin 6, Bitset.subset (blkFrame a.val t) (frameAt atlFrameTable s.val)
      = decide (s.val = blkToAtl a.val t) := fun s =>
    of_decide_eq_true (allFin_true _ (allLt_true _ _ (allFin_true _ S10Comp a) t ht) s)
  refine ⟨⟨blkToAtl a.val t, blkToAtl_lt a.val t a.isLt ht⟩, ?_, ?_⟩
  · rw [blkPart_part, key ⟨blkToAtl a.val t, blkToAtl_lt a.val t a.isLt ht⟩]
    exact decide_eq_true rfl
  · intro s hs
    rw [blkPart_part, key s] at hs
    exact Fin.eq_of_val_eq (of_decide_eq_true hs)

@[expose] public def resTab : Nat := 259194554488052909316

@[expose] public def resFrame (a : Nat) : Bitset := frameAt kFrameTable (byteAt resTab a)

public theorem resFrameComp : partOK (residue atlSet) resFrame 9 8 = true := by decide +kernel

@[expose] public def atlInKTab : Nat := 12124743139584

public theorem atlInKComp :
    allFin (fun i : Fin 6 => decide (frameAt atlFrameTable i.val
        = frameAt kFrameTable (byteAt atlInKTab i.val))
      && decide (byteAt atlInKTab i.val < 15)) = true := by decide +kernel

/-- `S11`. -/
public theorem S11 :
    (∀ i : Fin 6, ∃ j : Fin 15,
        frameAt atlFrameTable i.val = (partition_of_partOK kFrameComp).part j.val)
      ∧ Bitset.card (residue atlSet) = 72
      ∧ Nonempty (D54a (residue atlSet) 9 8)
      ∧ 6 + 9 = 15 := by
  refine ⟨fun i => ?_, by decide +kernel, ⟨partition_of_partOK resFrameComp⟩, rfl⟩
  have h := allFin_true _ atlInKComp i
  rw [Bool.and_eq_true] at h
  exact ⟨⟨byteAt atlInKTab i.val, of_decide_eq_true h.2⟩, of_decide_eq_true h.1⟩

/-- `S12`. -/
public theorem S12 :
    (3 : Nat) < 6 ∧ (6 : Nat) < 15
      ∧ Bitset.card fullK = 15 * 8
      ∧ Bitset.card atlSet = 6 * 8
      ∧ Bitset.card (blkSet 0) = 3 * 4
      ∧ ((6 : Rat) / 15 = (48 : Rat) / 120) := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, by decide +kernel⟩
  · exact S9 (partition_of_partOK kFrameComp)
  · exact S9 (partition_of_partOK atlFrameComp)
  · exact S9 (blkPart 0)


@[expose] public def B32 : Nat := 4294967296

@[expose] public def rowB (n : Nat) : Nat := B32 ^ n

@[expose] public def digitOf (B M j : Nat) : Nat := M / B ^ j % B

@[expose] public def bitAt (n aB i j : Nat) : Nat := (aB >>> (n * i + j)) % 2

public theorem bitAt_le_one (n aB i j : Nat) : bitAt n aB i j ≤ 1 := by
  show (aB >>> (n * i + j)) % 2 ≤ 1
  omega

@[expose] public def powA (n : Nat) (a : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, i, j => a i j
  | k + 1, i, j => sumN (fun l => a i l * powA n a k l j) n

@[expose] public def nextP (n aB M : Nat) : Nat :=
  pk (rowB n) (fun i => sumN (fun j => bitAt n aB i j * digitOf (rowB n) M j) n) n

@[expose] public def powP (n aB : Nat) : Nat → Nat
  | 0 => pk (rowB n) (fun i => pk B32 (fun j => bitAt n aB i j) n) n
  | k + 1 => nextP n aB (powP n aB k)

public theorem sumN_le (f : Nat → Nat) (B : Nat) (h : ∀ k, f k ≤ B) :
    ∀ m, sumN f m ≤ m * B := by
  intro m
  induction m with
  | zero => show (0 : Nat) ≤ 0 * B; omega
  | succ p ih =>
    show f p + sumN f p ≤ (p + 1) * B
    have hp := h p
    have hq : sumN f p ≤ p * B := ih
    have hm : (p + 1) * B = p * B + B := Nat.succ_mul p B
    omega

public theorem powA_le (n : Nat) (hn : 0 < n) (a : Nat → Nat → Nat) (ha : ∀ i j, a i j ≤ 1) :
    ∀ k i j, powA n a k i j ≤ n ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro i j
    show a i j ≤ n ^ 1
    rw [Nat.pow_one]
    have := ha i j
    omega
  | succ p ih =>
    intro i j
    show sumN (fun l => a i l * powA n a p l j) n ≤ n ^ (p + 2)
    have hb : ∀ l, a i l * powA n a p l j ≤ n ^ (p + 1) := by
      intro l
      exact Nat.le_trans (Nat.mul_le_mul (ha i l) (ih l j)) (by omega)
    have h1 := sumN_le _ _ hb n
    have h2 : n * n ^ (p + 1) = n ^ (p + 2) := (Nat.pow_succ' (m := n) (n := p + 1)).symm
    omega


public theorem rowB_pos (n : Nat) : 0 < rowB n :=
  Nat.pow_pos_iff.mpr (Or.inl (by decide))

public theorem digitOf_pk (B : Nat) (hB : 0 < B) (v : Nat → Nat) (m : Nat)
    (hv : ∀ k, k < m → v k < B) (j : Nat) (hj : j < m) : digitOf B (pk B v m) j = v j :=
  pk_digit B hB v m hv j hj

public theorem pk_congr (B : Nat) (v w : Nat → Nat) :
    ∀ m, (∀ k, k < m → v k = w k) → pk B v m = pk B w m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ p ih =>
    intro h
    rw [pk_succ, pk_succ, h p (Nat.lt_succ_self p), ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

/-- The packed powers are the powers: digit `(i,j)` of `powP k` is the `(i,j)`
entry of `A^(k+1)`. The packing is what makes the computation `n^2` row
additions per power rather than `n^3` scalar multiply-adds, exactly as `rowPk`
does for `A^2` in `UorAtlas.Roots`. -/
public theorem powP_eq (n aB : Nat) :
    ∀ k, (∀ t, t ≤ k → ∀ i j, powA n (bitAt n aB) t i j < B32) →
      powP n aB k
        = pk (rowB n) (fun i => pk B32 (fun j => powA n (bitAt n aB) k i j) n) n := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ p ih =>
    intro hb
    have hrow : ∀ j, pk B32 (fun c => powA n (bitAt n aB) p j c) n < rowB n :=
      fun j => pk_lt B32 _ n (fun c _ => hb p (Nat.le_succ p) j c)
    show nextP n aB (powP n aB p) = _
    rw [ih (fun t ht => hb t (Nat.le_succ_of_le ht))]
    show pk (rowB n) (fun i => sumN (fun j => bitAt n aB i j
      * digitOf (rowB n) (pk (rowB n)
          (fun i => pk B32 (fun j => powA n (bitAt n aB) p i j) n) n) j) n) n = _
    refine pk_congr (rowB n) _ _ n (fun i _ => ?_)
    have hdig : ∀ j, j < n → bitAt n aB i j
        * digitOf (rowB n) (pk (rowB n)
            (fun i => pk B32 (fun j => powA n (bitAt n aB) p i j) n) n) j
        = bitAt n aB i j * pk B32 (fun c => powA n (bitAt n aB) p j c) n := by
      intro j hj
      refine congrArg (fun t => bitAt n aB i j * t) ?_
      exact pk_digit (rowB n) (rowB_pos n) _ n (fun c _ => hrow c) j hj
    rw [sumN_congr_lt _ _ n hdig]
    exact pk_sumN B32 (bitAt n aB i) (fun j c => powA n (bitAt n aB) p j c) n n

@[expose] public def entryP (n aB k i j : Nat) : Nat :=
  digitOf B32 (digitOf (rowB n) (powP n aB k) i) j

public theorem entryP_eq (n aB : Nat) (k : Nat)
    (hb : ∀ t, t ≤ k → ∀ i j, powA n (bitAt n aB) t i j < B32)
    (i j : Nat) (hi : i < n) (hj : j < n) :
    entryP n aB k i j = powA n (bitAt n aB) k i j := by
  have hrow : ∀ c, pk B32 (fun d => powA n (bitAt n aB) k c d) n < rowB n :=
    fun c => pk_lt B32 _ n (fun d _ => hb k (Nat.le_refl k) c d)
  show digitOf B32 (digitOf (rowB n) (powP n aB k) i) j = _
  rw [powP_eq n aB k hb,
    digitOf_pk (rowB n) (rowB_pos n) _ n (fun c _ => hrow c) i hi]
  exact digitOf_pk B32 (by decide) _ n (fun d _ => hb k (Nat.le_refl k) i d) j hj

/-- A packed linear combination `sum_{k<5} c_k A^(k+1)`. -/
@[expose] public def combP (n aB : Nat) (c : Nat → Nat) : Nat :=
  sumN (fun k => c k * powP n aB k) 5

public theorem combP_eq (n aB : Nat) (c : Nat → Nat)
    (hb : ∀ t, t ≤ 4 → ∀ i j, powA n (bitAt n aB) t i j < B32) :
    combP n aB c
      = pk (rowB n) (fun i => pk B32 (fun j =>
          sumN (fun k => c k * powA n (bitAt n aB) k i j) 5) n) n := by
  have hstep : ∀ k, k < 5 → c k * powP n aB k
      = c k * pk (rowB n) (fun i => pk B32 (fun j => powA n (bitAt n aB) k i j) n) n := by
    intro k hk
    exact congrArg (fun t => c k * t) (powP_eq n aB k
      (fun t ht => hb t (Nat.le_trans ht (by omega))))
  show sumN (fun k => c k * powP n aB k) 5 = _
  rw [sumN_congr_lt _ _ 5 hstep,
    pk_sumN (rowB n) c (fun k i => pk B32 (fun j => powA n (bitAt n aB) k i j) n) n 5]
  refine pk_congr (rowB n) _ _ n (fun i _ => ?_)
  exact pk_sumN B32 c (fun k j => powA n (bitAt n aB) k i j) n 5


public theorem comb_entry (n aB : Nat) (cL cR : Nat → Nat)
    (hb : ∀ t, t ≤ 4 → ∀ i j, powA n (bitAt n aB) t i j < B32)
    (hbL : ∀ i j, sumN (fun k => cL k * powA n (bitAt n aB) k i j) 5 < B32)
    (hbR : ∀ i j, sumN (fun k => cR k * powA n (bitAt n aB) k i j) 5 < B32)
    (h : combP n aB cL = combP n aB cR) (i j : Nat) (hi : i < n) (hj : j < n) :
    sumN (fun k => cL k * powA n (bitAt n aB) k i j) 5
      = sumN (fun k => cR k * powA n (bitAt n aB) k i j) 5 := by
  rw [combP_eq n aB cL hb, combP_eq n aB cR hb] at h
  have hrow := pk_inj (rowB n) (rowB_pos n) _ _ n
    (fun c _ => pk_lt B32 _ n (fun d _ => hbL c d))
    (fun c _ => pk_lt B32 _ n (fun d _ => hbR c d)) h i hi
  exact pk_inj B32 (by decide) _ _ n (fun d _ => hbL i d) (fun d _ => hbR i d) hrow j hj

/-- `M^k`, with `M^0 = I`. -/
@[expose] public def mpowI {n : Nat} (M : Mat n n Int) : Nat → Mat n n Int
  | 0 => Mat.id
  | k + 1 => fun i j => Vec.sum (fun l => M i l * mpowI M k l j)

@[expose] public def traceI {n : Nat} (M : Mat n n Int) (k : Nat) : Int :=
  Vec.sumInt (fun i => mpowI M k i i)

public theorem isum_cast (n : Nat) (g : Nat → Nat) :
    Vec.sum (fun l : Fin n => ((g l.val : Nat) : Int)) = ((sumN g n : Nat) : Int) := by
  rw [← sumNat_cast (fun l : Fin n => g l.val)]
  exact congrArg (fun t : Nat => ((t : Nat) : Int)) (sumNat_eq_sumN n g)

public theorem mpowI_eq {n : Nat} (a : Nat → Nat → Nat) (M : Mat n n Int)
    (hM : ∀ i j : Fin n, M i j = ((a i.val j.val : Nat) : Int)) :
    ∀ k (i j : Fin n), mpowI M (k + 1) i j = ((powA n a k i.val j.val : Nat) : Int) := by
  intro k
  induction k with
  | zero =>
    intro i j
    have hterm : ∀ l : Fin n, mul (M i l) ((Mat.id : Mat n n Int) l j)
        = (if l = j then M i l else (AddCommGroup.zero : Int)) := by
      intro l
      by_cases hl : l = j
      · rw [if_pos hl]
        show M i l * (if l = j then (1 : Int) else 0) = M i l
        rw [if_pos hl]
        exact Int.mul_one _
      · rw [if_neg hl]
        show M i l * (if l = j then (1 : Int) else 0) = 0
        rw [if_neg hl]
        exact Int.mul_zero _
    show Vec.sum (fun l => mul (M i l) ((Mat.id : Mat n n Int) l j)) = _
    rw [Vec.sum_congr hterm, Vec.sum_ite_eq' j (fun l => M i l)]
    exact hM i j
  | succ p ih =>
    intro i j
    have hterm : ∀ l : Fin n, mul (M i l) (mpowI M (p + 1) l j)
        = ((a i.val l.val * powA n a p l.val j.val : Nat) : Int) := by
      intro l
      rw [ih l j, hM i l]
      exact (Int.natCast_mul _ _).symm
    show Vec.sum (fun l => mul (M i l) (mpowI M (p + 1) l j)) = _
    rw [Vec.sum_congr hterm, isum_cast n (fun l => a i.val l * powA n a p l j.val)]
    rfl

public theorem traceI_eq {n : Nat} (a : Nat → Nat → Nat) (M : Mat n n Int)
    (hM : ∀ i j : Fin n, M i j = ((a i.val j.val : Nat) : Int)) (k : Nat) :
    traceI M (k + 1) = ((sumN (fun i => powA n a k i i) n : Nat) : Int) := by
  show Vec.sumInt (fun i : Fin n => mpowI M (k + 1) i i) = _
  rw [Vec.sumInt_eq_sum, Vec.sum_congr (fun i : Fin n => mpowI_eq a M hM k i i)]
  exact isum_cast n (fun i => powA n a k i i)

public theorem traceI_zero {n : Nat} (M : Mat n n Int) : traceI M 0 = ((n : Nat) : Int) := by
  show Vec.sumInt (fun i : Fin n => (Mat.id : Mat n n Int) i i) = _
  rw [Vec.sumInt_eq_sum]
  have h : ∀ i : Fin n, (Mat.id : Mat n n Int) i i = (1 : Int) := by
    intro i
    show (if i = i then (1 : Int) else 0) = 1
    rw [if_pos rfl]
  rw [Vec.sum_congr h, isum_const, nsmulInt]
  omega


/-- The coefficients of `prod_{s<r} (x - lam s)`, lowest degree first. -/
@[expose] public def linProd (lam : Nat → Int) : Nat → Nat → Int
  | 0, k => if k = 0 then 1 else 0
  | r + 1, k => (if k = 0 then 0 else linProd lam r (k - 1)) - lam r * linProd lam r k

@[expose] public def D56 {n : Nat} (M : Mat n n Int) (r : Nat) (lam : Nat → Int)
    (mult : Nat → Nat) : Prop :=
  (∀ i j : Fin n, isumN (fun k => linProd lam r k * mpowI M k i j) (r + 1) = 0)
    /\ (∀ s t, s < r → t < r → s ≠ t → lam s ≠ lam t)
    /\ (∀ k, k < r → traceI M k = isumN (fun s => ((mult s : Nat) : Int) * lam s ^ k) r)
    /\ (∀ c : Nat → Nat,
        (∀ k, k < r → traceI M k = isumN (fun s => ((c s : Nat) : Int) * lam s ^ k) r)
        → ∀ s, s < r → c s = mult s)

@[expose] public def atlBits : Nat := 592138110129403994316306392716031439080783282590228723524131961588957430604615354313938522263239575141735944103734387250073313342384101615366162152232845164263210439844458850332091636246675639135532086976058963330725195409167788553160994288501589121868196545019556943618549121468523161275408667567186994738024645511201009603820460284907527311269808922426882932541658043756276996774987973911773578235326486740337730121561964014193662184983708049708041087418663797096647061898063135149219731146875973915955796723450355888614609364390301235969403043620428099105548060133744073596181629867674811400963203061113114476741660196795125822414022655264851760511566117560808235607405571254407593417785340

public theorem atlBitsComp :
    allLt (fun i => allLt (fun j => decide (bitAt 48 atlBits i j = adjN (xIdx i) (xIdx j))) 48) 48
      = true := by decide +kernel

@[expose] public def cAtlL : Nat → Nat := fun k =>
  if k = 1 then 448 else if k = 2 then 144 else if k = 4 then 1 else 0

@[expose] public def cAtlR : Nat → Nat := fun k =>
  if k = 0 then 2560 else if k = 3 then 28 else 0

public theorem atlAnnComp : combP 48 atlBits cAtlL = combP 48 atlBits cAtlR := by
  decide +kernel

@[expose] public def atlMat : Mat 48 48 Int :=
  fun i j => ((bitAt 48 atlBits i.val j.val : Nat) : Int)

public theorem atlBound : ∀ t, t ≤ 4 → ∀ i j,
    powA 48 (bitAt 48 atlBits) t i j < B32 := by
  intro t ht i j
  have h := powA_le 48 (by decide) (bitAt 48 atlBits) (bitAt_le_one 48 atlBits) t i j
  have h2 : (48 : Nat) ^ (t + 1) ≤ 48 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : (48 : Nat) ^ 5 < B32 := by decide
  omega

public theorem atlBoundL : ∀ i j,
    sumN (fun k => cAtlL k * powA 48 (bitAt 48 atlBits) k i j) 5 < B32 := by
  intro i j
  have h : ∀ t, powA 48 (bitAt 48 atlBits) t i j ≤ 48 ^ (t + 1) :=
    fun t => powA_le 48 (by decide) _ (bitAt_le_one 48 atlBits) t i j
  have h1 := h 1
  have h2 := h 2
  have h4 := h 4
  have e1 : (48 : Nat) ^ 2 = 2304 := by decide
  have e2 : (48 : Nat) ^ 3 = 110592 := by decide
  have e4 : (48 : Nat) ^ 5 = 254803968 := by decide
  rw [e1] at h1
  rw [e2] at h2
  rw [e4] at h4
  show 1 * powA 48 (bitAt 48 atlBits) 4 i j
      + (0 * powA 48 (bitAt 48 atlBits) 3 i j
      + (144 * powA 48 (bitAt 48 atlBits) 2 i j
      + (448 * powA 48 (bitAt 48 atlBits) 1 i j
      + (0 * powA 48 (bitAt 48 atlBits) 0 i j + 0)))) < 4294967296
  omega

public theorem atlBoundR : ∀ i j,
    sumN (fun k => cAtlR k * powA 48 (bitAt 48 atlBits) k i j) 5 < B32 := by
  intro i j
  have h : ∀ t, powA 48 (bitAt 48 atlBits) t i j ≤ 48 ^ (t + 1) :=
    fun t => powA_le 48 (by decide) _ (bitAt_le_one 48 atlBits) t i j
  have h0 := h 0
  have h3 := h 3
  have e0 : (48 : Nat) ^ 1 = 48 := by decide
  have e3 : (48 : Nat) ^ 4 = 5308416 := by decide
  rw [e0] at h0
  rw [e3] at h3
  show 0 * powA 48 (bitAt 48 atlBits) 4 i j
      + (28 * powA 48 (bitAt 48 atlBits) 3 i j
      + (0 * powA 48 (bitAt 48 atlBits) 2 i j
      + (0 * powA 48 (bitAt 48 atlBits) 1 i j
      + (2560 * powA 48 (bitAt 48 atlBits) 0 i j + 0)))) < 4294967296
  omega

public theorem atlMat_eq (i j : Fin 48) :
    atlMat i j = ((bitAt 48 atlBits i.val j.val : Nat) : Int) := rfl

public theorem atlEntry (i j : Fin 48) :
    448 * ((powA 48 (bitAt 48 atlBits) 1 i.val j.val : Nat) : Int)
      + 144 * ((powA 48 (bitAt 48 atlBits) 2 i.val j.val : Nat) : Int)
      + ((powA 48 (bitAt 48 atlBits) 4 i.val j.val : Nat) : Int)
      = 2560 * ((powA 48 (bitAt 48 atlBits) 0 i.val j.val : Nat) : Int)
        + 28 * ((powA 48 (bitAt 48 atlBits) 3 i.val j.val : Nat) : Int) := by
  have h := comb_entry 48 atlBits cAtlL cAtlR atlBound atlBoundL atlBoundR atlAnnComp
    i.val j.val i.isLt j.isLt
  have h' : 1 * powA 48 (bitAt 48 atlBits) 4 i.val j.val
      + (0 * powA 48 (bitAt 48 atlBits) 3 i.val j.val
      + (144 * powA 48 (bitAt 48 atlBits) 2 i.val j.val
      + (448 * powA 48 (bitAt 48 atlBits) 1 i.val j.val
      + (0 * powA 48 (bitAt 48 atlBits) 0 i.val j.val + 0))))
      = 0 * powA 48 (bitAt 48 atlBits) 4 i.val j.val
      + (28 * powA 48 (bitAt 48 atlBits) 3 i.val j.val
      + (0 * powA 48 (bitAt 48 atlBits) 2 i.val j.val
      + (0 * powA 48 (bitAt 48 atlBits) 1 i.val j.val
      + (2560 * powA 48 (bitAt 48 atlBits) 0 i.val j.val + 0)))) := h
  omega


@[expose] public def atlClass (i : Fin 48) : K := ⟨xIdx i.val % 120, Nat.mod_lt _ (by decide)⟩

public theorem atlMat_adj (i j : Fin 48) :
    atlMat i j = ((A (atlClass i) (atlClass j) : Nat) : Int) := by
  have hb := of_decide_eq_true (allLt_true _ _ (allLt_true _ _ atlBitsComp i.val i.isLt) j.val j.isLt)
  show ((bitAt 48 atlBits i.val j.val : Nat) : Int)
    = ((adjN (atlClass i).val (atlClass j).val : Nat) : Int)
  rw [hb]
  show ((adjN (xIdx i.val) (xIdx j.val) : Nat) : Int)
    = ((adjN (xIdx i.val % 120) (xIdx j.val % 120) : Nat) : Int)
  rw [Nat.mod_eq_of_lt (xIdx_lt i.val i.isLt), Nat.mod_eq_of_lt (xIdx_lt j.val j.isLt)]

public theorem atlTraceComp :
    sumN (fun i => entryP 48 atlBits 0 i i) 48 = 0
      ∧ sumN (fun i => entryP 48 atlBits 1 i i) 48 = 960
      ∧ sumN (fun i => entryP 48 atlBits 2 i i) 48 = 8448
      ∧ sumN (fun i => entryP 48 atlBits 3 i i) 48 = 175104 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

public theorem atlPowTrace (k : Nat) (hk : k ≤ 4) :
    sumN (fun i => powA 48 (bitAt 48 atlBits) k i i) 48
      = sumN (fun i => entryP 48 atlBits k i i) 48 := by
  refine (sumN_congr_lt _ _ 48 (fun i hi => ?_)).symm
  exact entryP_eq 48 atlBits k (fun t ht => atlBound t (Nat.le_trans ht hk)) i i hi hi

@[expose] public def atlLam : Nat → Int := fun s =>
  if s = 0 then 20 else if s = 1 then 8 else if s = 2 then 4 else if s = 3 then 0 else -4

@[expose] public def atlMult : Nat → Nat := fun s =>
  if s = 0 then 1 else if s = 1 then 2 else if s = 2 then 9 else if s = 3 then 18 else 18

@[expose] public def atlTraceVal : Nat → Int := fun k =>
  if k = 0 then 48 else if k = 1 then 0 else if k = 2 then 960
  else if k = 3 then 8448 else 175104

public theorem atlTrace : ∀ k, k < 5 → traceI atlMat k = atlTraceVal k := by
  have hstep : ∀ p, p ≤ 3 → traceI atlMat (p + 1)
      = ((sumN (fun i => entryP 48 atlBits p i i) 48 : Nat) : Int) := by
    intro p hp
    rw [traceI_eq (bitAt 48 atlBits) atlMat atlMat_eq p, atlPowTrace p (by omega)]
  intro k hk
  match k, hk with
  | 0, _ => rw [traceI_zero atlMat]; decide
  | 1, _ => rw [hstep 0 (by omega), atlTraceComp.1]; decide
  | 2, _ => rw [hstep 1 (by omega), atlTraceComp.2.1]; decide
  | 3, _ => rw [hstep 2 (by omega), atlTraceComp.2.2.1]; decide
  | 4, _ => rw [hstep 3 (by omega), atlTraceComp.2.2.2]; decide
  | (p + 5), h => exact absurd h (by omega)

/-- `S18`, `S20` and `S21` at the AtlasInstance: the spectrum of the class
graph induced on `X` is `{20^1, 8^2, 4^9, 0^18, (-4)^18}`, given exactly. -/
public theorem atlSpec : D56 atlMat 5 atlLam atlMult := by
  refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
  · have hE := atlEntry i j
    have h1 : mpowI atlMat 1 i j = ((powA 48 (bitAt 48 atlBits) 0 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 48 atlBits) atlMat atlMat_eq 0 i j
    have h2 : mpowI atlMat 2 i j = ((powA 48 (bitAt 48 atlBits) 1 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 48 atlBits) atlMat atlMat_eq 1 i j
    have h3 : mpowI atlMat 3 i j = ((powA 48 (bitAt 48 atlBits) 2 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 48 atlBits) atlMat atlMat_eq 2 i j
    have h4 : mpowI atlMat 4 i j = ((powA 48 (bitAt 48 atlBits) 3 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 48 atlBits) atlMat atlMat_eq 3 i j
    have h5 : mpowI atlMat 5 i j = ((powA 48 (bitAt 48 atlBits) 4 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 48 atlBits) atlMat atlMat_eq 4 i j
    have hl0 : linProd atlLam 5 0 = 0 := by decide
    have hl1 : linProd atlLam 5 1 = -2560 := by decide
    have hl2 : linProd atlLam 5 2 = 448 := by decide
    have hl3 : linProd atlLam 5 3 = 144 := by decide
    have hl4 : linProd atlLam 5 4 = -28 := by decide
    have hl5 : linProd atlLam 5 5 = 1 := by decide
    show linProd atlLam 5 5 * mpowI atlMat 5 i j
        + (linProd atlLam 5 4 * mpowI atlMat 4 i j
        + (linProd atlLam 5 3 * mpowI atlMat 3 i j
        + (linProd atlLam 5 2 * mpowI atlMat 2 i j
        + (linProd atlLam 5 1 * mpowI atlMat 1 i j
        + (linProd atlLam 5 0 * mpowI atlMat 0 i j + 0))))) = 0
    rw [hl0, hl1, hl2, hl3, hl4, hl5, h1, h2, h3, h4, h5]
    omega
  · have hd : ∀ s t : Fin 5, s ≠ t → atlLam s.val ≠ atlLam t.val := by decide
    intro s t hs ht hst
    exact hd ⟨s, hs⟩ ⟨t, ht⟩ (fun he => hst (congrArg Fin.val he))
  · intro k hk
    rw [atlTrace k hk]
    match k, hk with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | (p + 5), h => exact absurd h (by omega)
  · intro c hc
    have e0 := hc 0 (by omega)
    have e1 := hc 1 (by omega)
    have e2 := hc 2 (by omega)
    have e3 := hc 3 (by omega)
    have e4 := hc 4 (by omega)
    rw [atlTrace 0 (by omega)] at e0
    rw [atlTrace 1 (by omega)] at e1
    rw [atlTrace 2 (by omega)] at e2
    rw [atlTrace 3 (by omega)] at e3
    rw [atlTrace 4 (by omega)] at e4
    have f0 : (48 : Int) = ((c 4 : Nat) : Int) * 1 + (((c 3 : Nat) : Int) * 1
        + (((c 2 : Nat) : Int) * 1 + (((c 1 : Nat) : Int) * 1
        + (((c 0 : Nat) : Int) * 1 + 0)))) := e0
    have f1 : (0 : Int) = ((c 4 : Nat) : Int) * (-4) + (((c 3 : Nat) : Int) * 0
        + (((c 2 : Nat) : Int) * 4 + (((c 1 : Nat) : Int) * 8
        + (((c 0 : Nat) : Int) * 20 + 0)))) := e1
    have f2 : (960 : Int) = ((c 4 : Nat) : Int) * 16 + (((c 3 : Nat) : Int) * 0
        + (((c 2 : Nat) : Int) * 16 + (((c 1 : Nat) : Int) * 64
        + (((c 0 : Nat) : Int) * 400 + 0)))) := e2
    have f3 : (8448 : Int) = ((c 4 : Nat) : Int) * (-64) + (((c 3 : Nat) : Int) * 0
        + (((c 2 : Nat) : Int) * 64 + (((c 1 : Nat) : Int) * 512
        + (((c 0 : Nat) : Int) * 8000 + 0)))) := e3
    have f4 : (175104 : Int) = ((c 4 : Nat) : Int) * 256 + (((c 3 : Nat) : Int) * 0
        + (((c 2 : Nat) : Int) * 256 + (((c 1 : Nat) : Int) * 4096
        + (((c 0 : Nat) : Int) * 160000 + 0)))) := e4
    intro s hs
    match s, hs with
    | 0, _ => show c 0 = 1; omega
    | 1, _ => show c 1 = 2; omega
    | 2, _ => show c 2 = 9; omega
    | 3, _ => show c 3 = 18; omega
    | 4, _ => show c 4 = 18; omega
    | (p + 5), h => exact absurd h (by omega)


/-! ### The residue scale -/

@[expose] public def resBits : Nat := 1671494172085527506503739480136381367786144351735490040387601684921439357317451363450131478965790800520435967533094690264549673294540200648645292347065269022807272939190870316267461451098943122113825106559896568132826218189450141495735828936258406979694252593707749920876687826125002510714524950098780612296743193125450571320214128669796920363753544840024181099773925182882218208677098114736717984580435170924662992007360529723214332647947381972945380013626030885994432515742265821687158800422863468315972171854603312421975240891272626096814387124330422945472208365632894790377231953810512254461434301061231849405374947190373123537924004140393897606201104737587472148793231131436100033397163721531505603451173164814573988248603281044934662627262527324632771811106045590950292841708746176693411018269372305511436453225199231089418489274966333325395851151043887184079385978775616289058463820312270090707629569565001920697080891087715617734952825215132369703842812104303081766187185447912266477857562016131110340370711818911778597582938405805305163040878711534445222327337649057818791452076463334756095250946582631667647128859625402193185304775710740899148957275264271245304588690328971308699387456948711488807425972902379403121722144963373270678948990533725916407510726856231577699162419358074159544995013687809753815572015266098749609379507496278782800271202844839388284351570151387401419443698804701438744243208153483497607069062139065506179290229410804279756903776328213112641701649873109252476749007103364838366660957407591766551552912891410257089736645591100

@[expose] public def resIdxTable : Nat := 115417050284989515007038790838663465943082166896801932618844132463090222997437000281359348038567562193823916835767685342123527938206684662035009248119112941928301911301818632

@[expose] public def resIdx (i : Nat) : Nat := (resIdxTable >>> (8 * i)) &&& 255

public theorem resBitsComp :
    allLt (fun i => decide (resIdx i < 120)
      && allLt (fun j => decide (bitAt 72 resBits i j = adjN (resIdx i) (resIdx j))) 72) 72
      = true := by decide +kernel

public theorem resIdx_lt (i : Nat) (hi : i < 72) : resIdx i < 120 :=
  of_decide_eq_true (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ resBitsComp i hi)).1

@[expose] public def resClass (i : Fin 72) : K := ⟨resIdx i.val % 120, Nat.mod_lt _ (by decide)⟩

@[expose] public def resMat : Mat 72 72 Int :=
  fun i j => ((bitAt 72 resBits i.val j.val : Nat) : Int)

public theorem resMat_eq (i j : Fin 72) :
    resMat i j = ((bitAt 72 resBits i.val j.val : Nat) : Int) := rfl

public theorem resMat_adj (i j : Fin 72) :
    resMat i j = ((A (resClass i) (resClass j) : Nat) : Int) := by
  have hb := of_decide_eq_true (allLt_true _ _
    (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ resBitsComp i.val i.isLt)).2 j.val j.isLt)
  show ((bitAt 72 resBits i.val j.val : Nat) : Int)
    = ((adjN (resClass i).val (resClass j).val : Nat) : Int)
  rw [hb]
  show ((adjN (resIdx i.val) (resIdx j.val) : Nat) : Int)
    = ((adjN (resIdx i.val % 120) (resIdx j.val % 120) : Nat) : Int)
  rw [Nat.mod_eq_of_lt (resIdx_lt i.val i.isLt), Nat.mod_eq_of_lt (resIdx_lt j.val j.isLt)]

@[expose] public def cResL : Nat → Nat := fun k => if k = 1 then 640 else if k = 2 then 240 else if k = 4 then 1 else 0

@[expose] public def cResR : Nat → Nat := fun k => if k = 0 then 4096 else if k = 3 then 40 else 0

public theorem resAnnComp : combP 72 resBits cResL = combP 72 resBits cResR := by
  decide +kernel

public theorem resBound : ∀ t, t ≤ 4 → ∀ i j, powA 72 (bitAt 72 resBits) t i j < B32 := by
  intro t ht i j
  have h := powA_le 72 (by decide) (bitAt 72 resBits) (bitAt_le_one 72 resBits) t i j
  have h2 : (72 : Nat) ^ (t + 1) ≤ 72 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : (72 : Nat) ^ 5 < B32 := by decide
  omega

public theorem resBoundL : ∀ i j,
    sumN (fun k => cResL k * powA 72 (bitAt 72 resBits) k i j) 5 < B32 := by
  intro i j
  have h : ∀ t, powA 72 (bitAt 72 resBits) t i j ≤ 72 ^ (t + 1) :=
    fun t => powA_le 72 (by decide) _ (bitAt_le_one 72 resBits) t i j
  have hh1 := h 1
  have hh2 := h 2
  have hh4 := h 4
  have ee1 : (72 : Nat) ^ 2 = 5184 := by decide
  have ee2 : (72 : Nat) ^ 3 = 373248 := by decide
  have ee4 : (72 : Nat) ^ 5 = 1934917632 := by decide
  rw [ee1] at hh1
  rw [ee2] at hh2
  rw [ee4] at hh4
  show 1 * powA 72 (bitAt 72 resBits) 4 i j
      + (0 * powA 72 (bitAt 72 resBits) 3 i j
      + (240 * powA 72 (bitAt 72 resBits) 2 i j
      + (640 * powA 72 (bitAt 72 resBits) 1 i j
      + (0 * powA 72 (bitAt 72 resBits) 0 i j + 0)))) < 4294967296
  omega

public theorem resBoundR : ∀ i j,
    sumN (fun k => cResR k * powA 72 (bitAt 72 resBits) k i j) 5 < B32 := by
  intro i j
  have h : ∀ t, powA 72 (bitAt 72 resBits) t i j ≤ 72 ^ (t + 1) :=
    fun t => powA_le 72 (by decide) _ (bitAt_le_one 72 resBits) t i j
  have hh0 := h 0
  have hh3 := h 3
  have ee0 : (72 : Nat) ^ 1 = 72 := by decide
  have ee3 : (72 : Nat) ^ 4 = 26873856 := by decide
  rw [ee0] at hh0
  rw [ee3] at hh3
  show 0 * powA 72 (bitAt 72 resBits) 4 i j
      + (40 * powA 72 (bitAt 72 resBits) 3 i j
      + (0 * powA 72 (bitAt 72 resBits) 2 i j
      + (0 * powA 72 (bitAt 72 resBits) 1 i j
      + (4096 * powA 72 (bitAt 72 resBits) 0 i j + 0)))) < 4294967296
  omega

public theorem resEntry (i j : Fin 72) :
    640 * ((powA 72 (bitAt 72 resBits) 1 i.val j.val : Nat) : Int) + 240 * ((powA 72 (bitAt 72 resBits) 2 i.val j.val : Nat) : Int) + 1 * ((powA 72 (bitAt 72 resBits) 4 i.val j.val : Nat) : Int)
      = 4096 * ((powA 72 (bitAt 72 resBits) 0 i.val j.val : Nat) : Int) + 40 * ((powA 72 (bitAt 72 resBits) 3 i.val j.val : Nat) : Int) := by
  have h := comb_entry 72 resBits cResL cResR resBound resBoundL resBoundR resAnnComp
    i.val j.val i.isLt j.isLt
  have h' : 1 * powA 72 (bitAt 72 resBits) 4 i j
      + (0 * powA 72 (bitAt 72 resBits) 3 i j
      + (240 * powA 72 (bitAt 72 resBits) 2 i j
      + (640 * powA 72 (bitAt 72 resBits) 1 i j
      + (0 * powA 72 (bitAt 72 resBits) 0 i j + 0))))
      = 0 * powA 72 (bitAt 72 resBits) 4 i j
      + (40 * powA 72 (bitAt 72 resBits) 3 i j
      + (0 * powA 72 (bitAt 72 resBits) 2 i j
      + (0 * powA 72 (bitAt 72 resBits) 1 i j
      + (4096 * powA 72 (bitAt 72 resBits) 0 i j + 0)))) := h
  omega

public theorem resTraceComp :
    sumN (fun i => entryP 72 resBits 0 i i) 72 = 0
      ∧ sumN (fun i => entryP 72 resBits 1 i i) 72 = 2304
      ∧ sumN (fun i => entryP 72 resBits 2 i i) 72 = 34560
      ∧ sumN (fun i => entryP 72 resBits 3 i i) 72 = 1087488 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

public theorem resPowTrace (k : Nat) (hk : k ≤ 4) :
    sumN (fun i => powA 72 (bitAt 72 resBits) k i i) 72
      = sumN (fun i => entryP 72 resBits k i i) 72 := by
  refine (sumN_congr_lt _ _ 72 (fun i hi => ?_)).symm
  exact entryP_eq 72 resBits k (fun t ht => resBound t (Nat.le_trans ht hk)) i i hi hi

@[expose] public def resLam : Nat → Int := fun s => if s = 0 then 32 else if s = 1 then 8 else if s = 2 then 4 else if s = 3 then 0 else -4

@[expose] public def resMult : Nat → Nat := fun s => if s = 0 then 1 else if s = 1 then 6 else if s = 2 then 18 else if s = 3 then 9 else 38

@[expose] public def resTraceVal : Nat → Int := fun s => if s = 0 then 72 else if s = 1 then 0 else if s = 2 then 2304 else if s = 3 then 34560 else 1087488

public theorem resTrace : ∀ k, k < 5 → traceI resMat k = resTraceVal k := by
  have hstep : ∀ p, p ≤ 3 → traceI resMat (p + 1)
      = ((sumN (fun i => entryP 72 resBits p i i) 72 : Nat) : Int) := by
    intro p hp
    rw [traceI_eq (bitAt 72 resBits) resMat resMat_eq p, resPowTrace p (by omega)]
  intro k hk
  match k, hk with
  | 0, _ => rw [traceI_zero resMat]; decide
  | 1, _ => rw [hstep 0 (by omega), resTraceComp.1]; decide
  | 2, _ => rw [hstep 1 (by omega), resTraceComp.2.1]; decide
  | 3, _ => rw [hstep 2 (by omega), resTraceComp.2.2.1]; decide
  | 4, _ => rw [hstep 3 (by omega), resTraceComp.2.2.2]; decide
  | (p + 5), h => exact absurd h (by omega)

public theorem resSpec : D56 resMat 5 resLam resMult := by
  refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
  · have hE := resEntry i j
    have hp1 : mpowI resMat 1 i j = ((powA 72 (bitAt 72 resBits) 0 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 72 resBits) resMat resMat_eq 0 i j
    have hp2 : mpowI resMat 2 i j = ((powA 72 (bitAt 72 resBits) 1 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 72 resBits) resMat resMat_eq 1 i j
    have hp3 : mpowI resMat 3 i j = ((powA 72 (bitAt 72 resBits) 2 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 72 resBits) resMat resMat_eq 2 i j
    have hp4 : mpowI resMat 4 i j = ((powA 72 (bitAt 72 resBits) 3 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 72 resBits) resMat resMat_eq 3 i j
    have hp5 : mpowI resMat 5 i j = ((powA 72 (bitAt 72 resBits) 4 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 72 resBits) resMat resMat_eq 4 i j
    have hl0 : linProd resLam 5 0 = 0 := by decide
    have hl1 : linProd resLam 5 1 = -4096 := by decide
    have hl2 : linProd resLam 5 2 = 640 := by decide
    have hl3 : linProd resLam 5 3 = 240 := by decide
    have hl4 : linProd resLam 5 4 = -40 := by decide
    have hl5 : linProd resLam 5 5 = 1 := by decide
    show linProd resLam 5 5 * mpowI resMat 5 i j
        + (linProd resLam 5 4 * mpowI resMat 4 i j
        + (linProd resLam 5 3 * mpowI resMat 3 i j
        + (linProd resLam 5 2 * mpowI resMat 2 i j
        + (linProd resLam 5 1 * mpowI resMat 1 i j
        + (linProd resLam 5 0 * mpowI resMat 0 i j + 0))))) = 0
    rw [hl0, hl1, hl2, hl3, hl4, hl5, hp1, hp2, hp3, hp4, hp5]
    omega
  · have hd : ∀ s t : Fin 5, s ≠ t → resLam s.val ≠ resLam t.val := by decide
    intro s t hs ht hst
    exact hd ⟨s, hs⟩ ⟨t, ht⟩ (fun he => hst (congrArg Fin.val he))
  · intro k hk
    rw [resTrace k hk]
    match k, hk with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | (p + 5), h => exact absurd h (by omega)
  · intro c hc
    have e0 := hc 0 (by omega)
    have e1 := hc 1 (by omega)
    have e2 := hc 2 (by omega)
    have e3 := hc 3 (by omega)
    have e4 := hc 4 (by omega)
    rw [resTrace 0 (by omega)] at e0
    rw [resTrace 1 (by omega)] at e1
    rw [resTrace 2 (by omega)] at e2
    rw [resTrace 3 (by omega)] at e3
    rw [resTrace 4 (by omega)] at e4
    have f0 : (72 : Int) = ((c 4 : Nat) : Int) * (1)
        + (((c 3 : Nat) : Int) * (1)
        + (((c 2 : Nat) : Int) * (1)
        + (((c 1 : Nat) : Int) * (1)
        + (((c 0 : Nat) : Int) * (1) + 0)))) := e0
    have f1 : (0 : Int) = ((c 4 : Nat) : Int) * (-4)
        + (((c 3 : Nat) : Int) * (0)
        + (((c 2 : Nat) : Int) * (4)
        + (((c 1 : Nat) : Int) * (8)
        + (((c 0 : Nat) : Int) * (32) + 0)))) := e1
    have f2 : (2304 : Int) = ((c 4 : Nat) : Int) * (16)
        + (((c 3 : Nat) : Int) * (0)
        + (((c 2 : Nat) : Int) * (16)
        + (((c 1 : Nat) : Int) * (64)
        + (((c 0 : Nat) : Int) * (1024) + 0)))) := e2
    have f3 : (34560 : Int) = ((c 4 : Nat) : Int) * (-64)
        + (((c 3 : Nat) : Int) * (0)
        + (((c 2 : Nat) : Int) * (64)
        + (((c 1 : Nat) : Int) * (512)
        + (((c 0 : Nat) : Int) * (32768) + 0)))) := e3
    have f4 : (1087488 : Int) = ((c 4 : Nat) : Int) * (256)
        + (((c 3 : Nat) : Int) * (0)
        + (((c 2 : Nat) : Int) * (256)
        + (((c 1 : Nat) : Int) * (4096)
        + (((c 0 : Nat) : Int) * (1048576) + 0)))) := e4
    intro s hs
    match s, hs with
    | 0, _ => show c 0 = 1; omega
    | 1, _ => show c 1 = 6; omega
    | 2, _ => show c 2 = 18; omega
    | 3, _ => show c 3 = 9; omega
    | 4, _ => show c 4 = 38; omega
    | (p + 5), h => exact absurd h (by omega)

/-! ### The BlockFrame scale -/

@[expose] public def frmBits : Nat := 61591070444201922366005411144452046221843553996100480740953137434246213840580174088247782495259371368879087980890520782223343006445142534388102134248672145932550679193191420

@[expose] public def frmIdxTable : Nat := 1353788154356982868620270832306667596311458080241899143424

@[expose] public def frmIdx (i : Nat) : Nat := (frmIdxTable >>> (8 * i)) &&& 255

public theorem frmBitsComp :
    allLt (fun i => decide (frmIdx i < 120)
      && allLt (fun j => decide (bitAt 24 frmBits i j = adjN (frmIdx i) (frmIdx j))) 24) 24
      = true := by decide +kernel

public theorem frmIdx_lt (i : Nat) (hi : i < 24) : frmIdx i < 120 :=
  of_decide_eq_true (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ frmBitsComp i hi)).1

@[expose] public def frmClass (i : Fin 24) : K := ⟨frmIdx i.val % 120, Nat.mod_lt _ (by decide)⟩

@[expose] public def frmMat : Mat 24 24 Int :=
  fun i j => ((bitAt 24 frmBits i.val j.val : Nat) : Int)

public theorem frmMat_eq (i j : Fin 24) :
    frmMat i j = ((bitAt 24 frmBits i.val j.val : Nat) : Int) := rfl

public theorem frmMat_adj (i j : Fin 24) :
    frmMat i j = ((A (frmClass i) (frmClass j) : Nat) : Int) := by
  have hb := of_decide_eq_true (allLt_true _ _
    (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ frmBitsComp i.val i.isLt)).2 j.val j.isLt)
  show ((bitAt 24 frmBits i.val j.val : Nat) : Int)
    = ((adjN (frmClass i).val (frmClass j).val : Nat) : Int)
  rw [hb]
  show ((adjN (frmIdx i.val) (frmIdx j.val) : Nat) : Int)
    = ((adjN (frmIdx i.val % 120) (frmIdx j.val % 120) : Nat) : Int)
  rw [Nat.mod_eq_of_lt (frmIdx_lt i.val i.isLt), Nat.mod_eq_of_lt (frmIdx_lt j.val j.isLt)]

@[expose] public def cFrmL : Nat → Nat := fun k => if k = 2 then 1 else 0

@[expose] public def cFrmR : Nat → Nat := fun k => if k = 0 then 32 else if k = 1 then 4 else 0

public theorem frmAnnComp : combP 24 frmBits cFrmL = combP 24 frmBits cFrmR := by
  decide +kernel

public theorem frmBound : ∀ t, t ≤ 4 → ∀ i j, powA 24 (bitAt 24 frmBits) t i j < B32 := by
  intro t ht i j
  have h := powA_le 24 (by decide) (bitAt 24 frmBits) (bitAt_le_one 24 frmBits) t i j
  have h2 : (24 : Nat) ^ (t + 1) ≤ 24 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : (24 : Nat) ^ 5 < B32 := by decide
  omega

public theorem frmBoundL : ∀ i j,
    sumN (fun k => cFrmL k * powA 24 (bitAt 24 frmBits) k i j) 5 < B32 := by
  intro i j
  have h : ∀ t, powA 24 (bitAt 24 frmBits) t i j ≤ 24 ^ (t + 1) :=
    fun t => powA_le 24 (by decide) _ (bitAt_le_one 24 frmBits) t i j
  have hh2 := h 2
  have ee2 : (24 : Nat) ^ 3 = 13824 := by decide
  rw [ee2] at hh2
  show 0 * powA 24 (bitAt 24 frmBits) 4 i j
      + (0 * powA 24 (bitAt 24 frmBits) 3 i j
      + (1 * powA 24 (bitAt 24 frmBits) 2 i j
      + (0 * powA 24 (bitAt 24 frmBits) 1 i j
      + (0 * powA 24 (bitAt 24 frmBits) 0 i j + 0)))) < 4294967296
  omega

public theorem frmBoundR : ∀ i j,
    sumN (fun k => cFrmR k * powA 24 (bitAt 24 frmBits) k i j) 5 < B32 := by
  intro i j
  have h : ∀ t, powA 24 (bitAt 24 frmBits) t i j ≤ 24 ^ (t + 1) :=
    fun t => powA_le 24 (by decide) _ (bitAt_le_one 24 frmBits) t i j
  have hh0 := h 0
  have hh1 := h 1
  have ee0 : (24 : Nat) ^ 1 = 24 := by decide
  have ee1 : (24 : Nat) ^ 2 = 576 := by decide
  rw [ee0] at hh0
  rw [ee1] at hh1
  show 0 * powA 24 (bitAt 24 frmBits) 4 i j
      + (0 * powA 24 (bitAt 24 frmBits) 3 i j
      + (0 * powA 24 (bitAt 24 frmBits) 2 i j
      + (4 * powA 24 (bitAt 24 frmBits) 1 i j
      + (32 * powA 24 (bitAt 24 frmBits) 0 i j + 0)))) < 4294967296
  omega

public theorem frmEntry (i j : Fin 24) :
    1 * ((powA 24 (bitAt 24 frmBits) 2 i.val j.val : Nat) : Int)
      = 32 * ((powA 24 (bitAt 24 frmBits) 0 i.val j.val : Nat) : Int) + 4 * ((powA 24 (bitAt 24 frmBits) 1 i.val j.val : Nat) : Int) := by
  have h := comb_entry 24 frmBits cFrmL cFrmR frmBound frmBoundL frmBoundR frmAnnComp
    i.val j.val i.isLt j.isLt
  have h' : 0 * powA 24 (bitAt 24 frmBits) 4 i j
      + (0 * powA 24 (bitAt 24 frmBits) 3 i j
      + (1 * powA 24 (bitAt 24 frmBits) 2 i j
      + (0 * powA 24 (bitAt 24 frmBits) 1 i j
      + (0 * powA 24 (bitAt 24 frmBits) 0 i j + 0))))
      = 0 * powA 24 (bitAt 24 frmBits) 4 i j
      + (0 * powA 24 (bitAt 24 frmBits) 3 i j
      + (0 * powA 24 (bitAt 24 frmBits) 2 i j
      + (4 * powA 24 (bitAt 24 frmBits) 1 i j
      + (32 * powA 24 (bitAt 24 frmBits) 0 i j + 0)))) := h
  omega

public theorem frmTraceComp :
    sumN (fun i => entryP 24 frmBits 0 i i) 24 = 0
      ∧ sumN (fun i => entryP 24 frmBits 1 i i) 24 = 192 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

public theorem frmPowTrace (k : Nat) (hk : k ≤ 4) :
    sumN (fun i => powA 24 (bitAt 24 frmBits) k i i) 24
      = sumN (fun i => entryP 24 frmBits k i i) 24 := by
  refine (sumN_congr_lt _ _ 24 (fun i hi => ?_)).symm
  exact entryP_eq 24 frmBits k (fun t ht => frmBound t (Nat.le_trans ht hk)) i i hi hi

@[expose] public def frmLam : Nat → Int := fun s => if s = 0 then 8 else if s = 1 then 0 else -4

@[expose] public def frmMult : Nat → Nat := fun s => if s = 0 then 2 else if s = 1 then 18 else 4

@[expose] public def frmTraceVal : Nat → Int := fun s => if s = 0 then 24 else if s = 1 then 0 else 192

public theorem frmTrace : ∀ k, k < 3 → traceI frmMat k = frmTraceVal k := by
  have hstep : ∀ p, p ≤ 1 → traceI frmMat (p + 1)
      = ((sumN (fun i => entryP 24 frmBits p i i) 24 : Nat) : Int) := by
    intro p hp
    rw [traceI_eq (bitAt 24 frmBits) frmMat frmMat_eq p, frmPowTrace p (by omega)]
  intro k hk
  match k, hk with
  | 0, _ => rw [traceI_zero frmMat]; decide
  | 1, _ => rw [hstep 0 (by omega), frmTraceComp.1]; decide
  | 2, _ => rw [hstep 1 (by omega), frmTraceComp.2]; decide
  | (p + 3), h => exact absurd h (by omega)

public theorem frmSpec : D56 frmMat 3 frmLam frmMult := by
  refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
  · have hE := frmEntry i j
    have hp1 : mpowI frmMat 1 i j = ((powA 24 (bitAt 24 frmBits) 0 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 24 frmBits) frmMat frmMat_eq 0 i j
    have hp2 : mpowI frmMat 2 i j = ((powA 24 (bitAt 24 frmBits) 1 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 24 frmBits) frmMat frmMat_eq 1 i j
    have hp3 : mpowI frmMat 3 i j = ((powA 24 (bitAt 24 frmBits) 2 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 24 frmBits) frmMat frmMat_eq 2 i j
    have hl0 : linProd frmLam 3 0 = 0 := by decide
    have hl1 : linProd frmLam 3 1 = -32 := by decide
    have hl2 : linProd frmLam 3 2 = -4 := by decide
    have hl3 : linProd frmLam 3 3 = 1 := by decide
    show linProd frmLam 3 3 * mpowI frmMat 3 i j
        + (linProd frmLam 3 2 * mpowI frmMat 2 i j
        + (linProd frmLam 3 1 * mpowI frmMat 1 i j
        + (linProd frmLam 3 0 * mpowI frmMat 0 i j + 0))) = 0
    rw [hl0, hl1, hl2, hl3, hp1, hp2, hp3]
    omega
  · have hd : ∀ s t : Fin 3, s ≠ t → frmLam s.val ≠ frmLam t.val := by decide
    intro s t hs ht hst
    exact hd ⟨s, hs⟩ ⟨t, ht⟩ (fun he => hst (congrArg Fin.val he))
  · intro k hk
    rw [frmTrace k hk]
    match k, hk with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | (p + 3), h => exact absurd h (by omega)
  · intro c hc
    have e0 := hc 0 (by omega)
    have e1 := hc 1 (by omega)
    have e2 := hc 2 (by omega)
    rw [frmTrace 0 (by omega)] at e0
    rw [frmTrace 1 (by omega)] at e1
    rw [frmTrace 2 (by omega)] at e2
    have f0 : (24 : Int) = ((c 2 : Nat) : Int) * (1)
        + (((c 1 : Nat) : Int) * (1)
        + (((c 0 : Nat) : Int) * (1) + 0)) := e0
    have f1 : (0 : Int) = ((c 2 : Nat) : Int) * (-4)
        + (((c 1 : Nat) : Int) * (0)
        + (((c 0 : Nat) : Int) * (8) + 0)) := e1
    have f2 : (192 : Int) = ((c 2 : Nat) : Int) * (16)
        + (((c 1 : Nat) : Int) * (0)
        + (((c 0 : Nat) : Int) * (64) + 0)) := e2
    intro s hs
    match s, hs with
    | 0, _ => show c 0 = 2; omega
    | 1, _ => show c 1 = 18; omega
    | 2, _ => show c 2 = 4; omega
    | (p + 3), h => exact absurd h (by omega)

/-! ### The block scale -/

@[expose] public def blkBits : Nat := 5554765116747137659085743261276883044516860

@[expose] public def blkIdxTable : Nat := 8387607912949221252464247040

@[expose] public def blkIdx (i : Nat) : Nat := (blkIdxTable >>> (8 * i)) &&& 255

public theorem blkBitsComp :
    allLt (fun i => decide (blkIdx i < 120)
      && allLt (fun j => decide (bitAt 12 blkBits i j = adjN (blkIdx i) (blkIdx j))) 12) 12
      = true := by decide +kernel

public theorem blkIdx_lt (i : Nat) (hi : i < 12) : blkIdx i < 120 :=
  of_decide_eq_true (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ blkBitsComp i hi)).1

@[expose] public def blkClass (i : Fin 12) : K := ⟨blkIdx i.val % 120, Nat.mod_lt _ (by decide)⟩

@[expose] public def blkMat : Mat 12 12 Int :=
  fun i j => ((bitAt 12 blkBits i.val j.val : Nat) : Int)

public theorem blkMat_eq (i j : Fin 12) :
    blkMat i j = ((bitAt 12 blkBits i.val j.val : Nat) : Int) := rfl

public theorem blkMat_adj (i j : Fin 12) :
    blkMat i j = ((A (blkClass i) (blkClass j) : Nat) : Int) := by
  have hb := of_decide_eq_true (allLt_true _ _
    (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ blkBitsComp i.val i.isLt)).2 j.val j.isLt)
  show ((bitAt 12 blkBits i.val j.val : Nat) : Int)
    = ((adjN (blkClass i).val (blkClass j).val : Nat) : Int)
  rw [hb]
  show ((adjN (blkIdx i.val) (blkIdx j.val) : Nat) : Int)
    = ((adjN (blkIdx i.val % 120) (blkIdx j.val % 120) : Nat) : Int)
  rw [Nat.mod_eq_of_lt (blkIdx_lt i.val i.isLt), Nat.mod_eq_of_lt (blkIdx_lt j.val j.isLt)]

@[expose] public def cBlkL : Nat → Nat := fun k => if k = 2 then 1 else 0

@[expose] public def cBlkR : Nat → Nat := fun k => if k = 0 then 32 else if k = 1 then 4 else 0

public theorem blkAnnComp : combP 12 blkBits cBlkL = combP 12 blkBits cBlkR := by
  decide +kernel

public theorem blkBound : ∀ t, t ≤ 4 → ∀ i j, powA 12 (bitAt 12 blkBits) t i j < B32 := by
  intro t ht i j
  have h := powA_le 12 (by decide) (bitAt 12 blkBits) (bitAt_le_one 12 blkBits) t i j
  have h2 : (12 : Nat) ^ (t + 1) ≤ 12 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : (12 : Nat) ^ 5 < B32 := by decide
  omega

public theorem blkBoundL : ∀ i j,
    sumN (fun k => cBlkL k * powA 12 (bitAt 12 blkBits) k i j) 5 < B32 := by
  intro i j
  have h : ∀ t, powA 12 (bitAt 12 blkBits) t i j ≤ 12 ^ (t + 1) :=
    fun t => powA_le 12 (by decide) _ (bitAt_le_one 12 blkBits) t i j
  have hh2 := h 2
  have ee2 : (12 : Nat) ^ 3 = 1728 := by decide
  rw [ee2] at hh2
  show 0 * powA 12 (bitAt 12 blkBits) 4 i j
      + (0 * powA 12 (bitAt 12 blkBits) 3 i j
      + (1 * powA 12 (bitAt 12 blkBits) 2 i j
      + (0 * powA 12 (bitAt 12 blkBits) 1 i j
      + (0 * powA 12 (bitAt 12 blkBits) 0 i j + 0)))) < 4294967296
  omega

public theorem blkBoundR : ∀ i j,
    sumN (fun k => cBlkR k * powA 12 (bitAt 12 blkBits) k i j) 5 < B32 := by
  intro i j
  have h : ∀ t, powA 12 (bitAt 12 blkBits) t i j ≤ 12 ^ (t + 1) :=
    fun t => powA_le 12 (by decide) _ (bitAt_le_one 12 blkBits) t i j
  have hh0 := h 0
  have hh1 := h 1
  have ee0 : (12 : Nat) ^ 1 = 12 := by decide
  have ee1 : (12 : Nat) ^ 2 = 144 := by decide
  rw [ee0] at hh0
  rw [ee1] at hh1
  show 0 * powA 12 (bitAt 12 blkBits) 4 i j
      + (0 * powA 12 (bitAt 12 blkBits) 3 i j
      + (0 * powA 12 (bitAt 12 blkBits) 2 i j
      + (4 * powA 12 (bitAt 12 blkBits) 1 i j
      + (32 * powA 12 (bitAt 12 blkBits) 0 i j + 0)))) < 4294967296
  omega

public theorem blkEntry (i j : Fin 12) :
    1 * ((powA 12 (bitAt 12 blkBits) 2 i.val j.val : Nat) : Int)
      = 32 * ((powA 12 (bitAt 12 blkBits) 0 i.val j.val : Nat) : Int) + 4 * ((powA 12 (bitAt 12 blkBits) 1 i.val j.val : Nat) : Int) := by
  have h := comb_entry 12 blkBits cBlkL cBlkR blkBound blkBoundL blkBoundR blkAnnComp
    i.val j.val i.isLt j.isLt
  have h' : 0 * powA 12 (bitAt 12 blkBits) 4 i j
      + (0 * powA 12 (bitAt 12 blkBits) 3 i j
      + (1 * powA 12 (bitAt 12 blkBits) 2 i j
      + (0 * powA 12 (bitAt 12 blkBits) 1 i j
      + (0 * powA 12 (bitAt 12 blkBits) 0 i j + 0))))
      = 0 * powA 12 (bitAt 12 blkBits) 4 i j
      + (0 * powA 12 (bitAt 12 blkBits) 3 i j
      + (0 * powA 12 (bitAt 12 blkBits) 2 i j
      + (4 * powA 12 (bitAt 12 blkBits) 1 i j
      + (32 * powA 12 (bitAt 12 blkBits) 0 i j + 0)))) := h
  omega

public theorem blkTraceComp :
    sumN (fun i => entryP 12 blkBits 0 i i) 12 = 0
      ∧ sumN (fun i => entryP 12 blkBits 1 i i) 12 = 96 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

public theorem blkPowTrace (k : Nat) (hk : k ≤ 4) :
    sumN (fun i => powA 12 (bitAt 12 blkBits) k i i) 12
      = sumN (fun i => entryP 12 blkBits k i i) 12 := by
  refine (sumN_congr_lt _ _ 12 (fun i hi => ?_)).symm
  exact entryP_eq 12 blkBits k (fun t ht => blkBound t (Nat.le_trans ht hk)) i i hi hi

@[expose] public def blkLam : Nat → Int := fun s => if s = 0 then 8 else if s = 1 then 0 else -4

@[expose] public def blkMult : Nat → Nat := fun s => if s = 0 then 1 else if s = 1 then 9 else 2

@[expose] public def blkTraceVal : Nat → Int := fun s => if s = 0 then 12 else if s = 1 then 0 else 96

public theorem blkTrace : ∀ k, k < 3 → traceI blkMat k = blkTraceVal k := by
  have hstep : ∀ p, p ≤ 1 → traceI blkMat (p + 1)
      = ((sumN (fun i => entryP 12 blkBits p i i) 12 : Nat) : Int) := by
    intro p hp
    rw [traceI_eq (bitAt 12 blkBits) blkMat blkMat_eq p, blkPowTrace p (by omega)]
  intro k hk
  match k, hk with
  | 0, _ => rw [traceI_zero blkMat]; decide
  | 1, _ => rw [hstep 0 (by omega), blkTraceComp.1]; decide
  | 2, _ => rw [hstep 1 (by omega), blkTraceComp.2]; decide
  | (p + 3), h => exact absurd h (by omega)

public theorem blkSpec : D56 blkMat 3 blkLam blkMult := by
  refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
  · have hE := blkEntry i j
    have hp1 : mpowI blkMat 1 i j = ((powA 12 (bitAt 12 blkBits) 0 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 12 blkBits) blkMat blkMat_eq 0 i j
    have hp2 : mpowI blkMat 2 i j = ((powA 12 (bitAt 12 blkBits) 1 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 12 blkBits) blkMat blkMat_eq 1 i j
    have hp3 : mpowI blkMat 3 i j = ((powA 12 (bitAt 12 blkBits) 2 i.val j.val : Nat) : Int) :=
      mpowI_eq (bitAt 12 blkBits) blkMat blkMat_eq 2 i j
    have hl0 : linProd blkLam 3 0 = 0 := by decide
    have hl1 : linProd blkLam 3 1 = -32 := by decide
    have hl2 : linProd blkLam 3 2 = -4 := by decide
    have hl3 : linProd blkLam 3 3 = 1 := by decide
    show linProd blkLam 3 3 * mpowI blkMat 3 i j
        + (linProd blkLam 3 2 * mpowI blkMat 2 i j
        + (linProd blkLam 3 1 * mpowI blkMat 1 i j
        + (linProd blkLam 3 0 * mpowI blkMat 0 i j + 0))) = 0
    rw [hl0, hl1, hl2, hl3, hp1, hp2, hp3]
    omega
  · have hd : ∀ s t : Fin 3, s ≠ t → blkLam s.val ≠ blkLam t.val := by decide
    intro s t hs ht hst
    exact hd ⟨s, hs⟩ ⟨t, ht⟩ (fun he => hst (congrArg Fin.val he))
  · intro k hk
    rw [blkTrace k hk]
    match k, hk with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | (p + 3), h => exact absurd h (by omega)
  · intro c hc
    have e0 := hc 0 (by omega)
    have e1 := hc 1 (by omega)
    have e2 := hc 2 (by omega)
    rw [blkTrace 0 (by omega)] at e0
    rw [blkTrace 1 (by omega)] at e1
    rw [blkTrace 2 (by omega)] at e2
    have f0 : (12 : Int) = ((c 2 : Nat) : Int) * (1)
        + (((c 1 : Nat) : Int) * (1)
        + (((c 0 : Nat) : Int) * (1) + 0)) := e0
    have f1 : (0 : Int) = ((c 2 : Nat) : Int) * (-4)
        + (((c 1 : Nat) : Int) * (0)
        + (((c 0 : Nat) : Int) * (8) + 0)) := e1
    have f2 : (96 : Int) = ((c 2 : Nat) : Int) * (16)
        + (((c 1 : Nat) : Int) * (0)
        + (((c 0 : Nat) : Int) * (64) + 0)) := e2
    intro s hs
    match s, hs with
    | 0, _ => show c 0 = 1; omega
    | 1, _ => show c 1 = 9; omega
    | 2, _ => show c 2 = 2; omega
    | (p + 3), h => exact absurd h (by omega)


/-! ### The ambient scale

`T9a` already annihilates `A` on `K`, and `comb_mul` closes the three
dimensional algebra it lives in, so the ambient row of the tower needs no new
kernel computation: `A^2` and `A^3` are read off the multiplication table and
the traces are the `trI`, `trA`, `trA2` of `UorAtlas.Roots`. -/

public theorem mpowI_one {n : Nat} (M : Mat n n Int) (i j : Fin n) : mpowI M 1 i j = M i j := by
  have hterm : ∀ l : Fin n, mul (M i l) ((Mat.id : Mat n n Int) l j)
      = (if l = j then M i l else (AddCommGroup.zero : Int)) := by
    intro l
    by_cases hl : l = j
    · rw [if_pos hl]
      show M i l * (if l = j then (1 : Int) else 0) = M i l
      rw [if_pos hl]
      exact Int.mul_one _
    · rw [if_neg hl]
      show M i l * (if l = j then (1 : Int) else 0) = 0
      rw [if_neg hl]
      exact Int.mul_zero _
  show Vec.sum (fun l => mul (M i l) ((Mat.id : Mat n n Int) l j)) = _
  rw [Vec.sum_congr hterm, Vec.sum_ite_eq' j (fun l => M i l)]

public theorem mpowI_Aint_one : mpowI Aint 1 = Aint := by
  funext u v; exact mpowI_one Aint u v

public theorem Aint_comb : Aint = comb 0 1 0 := by
  funext u v
  show ((A u v : Nat) : Int) = 0 * (if u = v then 1 else 0) + 1 * ((A u v : Nat) : Int) + 0
  split <;> omega

public theorem ambPow2 : mpowI Aint 2 = comb 32 4 24 := by
  funext i j
  show Mat.mul Aint (mpowI Aint 1) i j = comb 32 4 24 i j
  rw [mpowI_Aint_one, Aint_comb, comb_mul 0 1 0 0 1 0 i j]
  rfl

public theorem ambPow3 : mpowI Aint 3 = comb 128 48 1440 := by
  funext i j
  show Mat.mul Aint (mpowI Aint 2) i j = comb 128 48 1440 i j
  rw [ambPow2, Aint_comb, comb_mul 0 1 0 32 4 24 i j]
  rfl

@[expose] public def ambLam : Nat → Int := fun s => if s = 0 then 56 else if s = 1 then 8 else -4

@[expose] public def ambMult : Nat → Nat := fun s => if s = 0 then 1 else if s = 1 then 35 else 84

@[expose] public def ambTraceVal : Nat → Int := fun s =>
  if s = 0 then 120 else if s = 1 then 0 else 6720

public theorem ambTrace : ∀ k, k < 3 → traceI Aint k = ambTraceVal k := by
  intro k hk
  match k, hk with
  | 0, _ => rw [traceI_zero Aint]; decide
  | 1, _ =>
    show Vec.sumInt (fun i : K => mpowI Aint 1 i i) = ambTraceVal 1
    rw [Vec.sumInt_eq_sum, Vec.sum_congr (fun i : K => mpowI_one Aint i i)]
    show trA = ambTraceVal 1
    rw [trA_eq]
    decide
  | 2, _ =>
    show Vec.sumInt (fun i : K => mpowI Aint 2 i i) = ambTraceVal 2
    rw [Vec.sumInt_eq_sum]
    have h : ∀ i : K, mpowI Aint 2 i i = Mat.mul Aint Aint i i := by
      intro i
      show Mat.mul Aint (mpowI Aint 1) i i = Mat.mul Aint Aint i i
      rw [mpowI_Aint_one]
    rw [Vec.sum_congr h]
    show trA2 = ambTraceVal 2
    rw [trA2_eq]
    decide
  | (p + 3), h => exact absurd h (by omega)

/-- The ambient row of the tower, in the shape `T9` gives it. -/
public theorem ambSpec : D56 Aint 3 ambLam ambMult := by
  refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
  · have hl0 : linProd ambLam 3 0 = 1792 := by decide
    have hl1 : linProd ambLam 3 1 = 192 := by decide
    have hl2 : linProd ambLam 3 2 = -60 := by decide
    have hl3 : linProd ambLam 3 3 = 1 := by decide
    have h1 : mpowI Aint 1 i j = Aint i j := mpowI_one Aint i j
    have h2 : mpowI Aint 2 i j = comb 32 4 24 i j := congrFun (congrFun ambPow2 i) j
    have h3 : mpowI Aint 3 i j = comb 128 48 1440 i j := congrFun (congrFun ambPow3 i) j
    show linProd ambLam 3 3 * mpowI Aint 3 i j
        + (linProd ambLam 3 2 * mpowI Aint 2 i j
        + (linProd ambLam 3 1 * mpowI Aint 1 i j
        + (linProd ambLam 3 0 * mpowI Aint 0 i j + 0))) = 0
    rw [hl0, hl1, hl2, hl3, h1, h2, h3]
    show (1 : Int) * (128 * (if i = j then 1 else 0) + 48 * Aint i j + 1440)
        + ((-60) * (32 * (if i = j then 1 else 0) + 4 * Aint i j + 24)
        + (192 * Aint i j
        + (1792 * (if i = j then (1 : Int) else 0) + 0))) = 0
    split <;> omega
  · have hd : ∀ s t : Fin 3, s ≠ t → ambLam s.val ≠ ambLam t.val := by decide
    intro s t hs ht hst
    exact hd ⟨s, hs⟩ ⟨t, ht⟩ (fun he => hst (congrArg Fin.val he))
  · intro k hk
    rw [ambTrace k hk]
    match k, hk with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | (p + 3), h => exact absurd h (by omega)
  · intro c hc
    have e0 := hc 0 (by omega)
    have e1 := hc 1 (by omega)
    have e2 := hc 2 (by omega)
    rw [ambTrace 0 (by omega)] at e0
    rw [ambTrace 1 (by omega)] at e1
    rw [ambTrace 2 (by omega)] at e2
    have f0 : (120 : Int) = ((c 2 : Nat) : Int) * 1
        + (((c 1 : Nat) : Int) * 1 + (((c 0 : Nat) : Int) * 1 + 0)) := e0
    have f1 : (0 : Int) = ((c 2 : Nat) : Int) * (-4)
        + (((c 1 : Nat) : Int) * 8 + (((c 0 : Nat) : Int) * 56 + 0)) := e1
    have f2 : (6720 : Int) = ((c 2 : Nat) : Int) * 16
        + (((c 1 : Nat) : Int) * 64 + (((c 0 : Nat) : Int) * 3136 + 0)) := e2
    intro s hs
    match s, hs with
    | 0, _ => show c 0 = 1; omega
    | 1, _ => show c 1 = 35; omega
    | 2, _ => show c 2 = 84; omega
    | (p + 3), h => exact absurd h (by omega)


/-! ## `S18`, `S20`, `S21`, `S32`: the tower read off the five spectra -/

/-- The values the non-principal spectrum is allowed to take. -/
@[expose] public def SpecOK (lam : Nat → Int) (r : Nat) : Prop :=
  ∀ s, 0 < s → s < r → (lam s = 8 ∨ lam s = 4 ∨ lam s = 0 ∨ lam s = -4)

/-- `S18`. On the five scales of the tower the non-principal spectrum is
confined to `{8,4,0,-4}`, and the principal eigenvalue is the degree. -/
public theorem S18 :
    (SpecOK ambLam 3 ∧ ambLam 0 = 56)
      ∧ (SpecOK resLam 5 ∧ resLam 0 = 32)
      ∧ (SpecOK atlLam 5 ∧ atlLam 0 = 20)
      ∧ (SpecOK frmLam 3 ∧ frmLam 0 = 8)
      ∧ (SpecOK blkLam 3 ∧ blkLam 0 = 8) := by
  refine ⟨⟨?_, by decide⟩, ⟨?_, by decide⟩, ⟨?_, by decide⟩, ⟨?_, by decide⟩, ⟨?_, by decide⟩⟩ <;>
    (intro s hs hr
     match s, hs, hr with
     | 1, _, _ => decide
     | 2, _, _ => decide
     | 3, _, _ => decide
     | 4, _, _ => decide
     | 0, h, _ => exact absurd h (by omega)
     | (p + 5), _, h => exact absurd h (by omega))

/-- `S20`. Every eigenvalue at every tower scale is divisible by `4`. -/
public theorem S20 :
    (∀ s, s < 3 → ambLam s % 4 = 0)
      ∧ (∀ s, s < 5 → resLam s % 4 = 0)
      ∧ (∀ s, s < 5 → atlLam s % 4 = 0)
      ∧ (∀ s, s < 3 → frmLam s % 4 = 0)
      ∧ (∀ s, s < 3 → blkLam s % 4 = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro s hs
     match s, hs with
     | 0, _ => decide
     | 1, _ => decide
     | 2, _ => decide
     | 3, _ => decide
     | 4, _ => decide
     | (p + 5), h => exact absurd h (by omega))

/-- `S21`. The AtlasInstance and its residue swap multiplicities at `4` and
`0`: `4^9 0^18` against `4^18 0^9`. -/
public theorem S21 :
    (atlLam 2 = 4 ∧ atlMult 2 = 9 ∧ atlLam 3 = 0 ∧ atlMult 3 = 18)
      ∧ (resLam 2 = 4 ∧ resMult 2 = 18 ∧ resLam 3 = 0 ∧ resMult 3 = 9) := by
  refine ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩⟩

/-- `S32`. `S18` and `S20` are proved for the tower in the shape `D56`
prescribes -- an annihilating polynomial over `Z` together with integer traces
whose linear system has a unique nonnegative integer solution -- and the five
matrices are the class graphs induced on the five scales, not abstract
matrices. This is a proof about one specific finite graph, not a measurement. -/
public theorem S32 :
    D56 Aint 3 ambLam ambMult
      ∧ D56 resMat 5 resLam resMult
      ∧ D56 atlMat 5 atlLam atlMult
      ∧ D56 frmMat 3 frmLam frmMult
      ∧ D56 blkMat 3 blkLam blkMult
      ∧ (∀ i j : Fin 72, resMat i j = ((A (resClass i) (resClass j) : Nat) : Int))
      ∧ (∀ i j : Fin 48, atlMat i j = ((A (atlClass i) (atlClass j) : Nat) : Int))
      ∧ (∀ i j : Fin 24, frmMat i j = ((A (frmClass i) (frmClass j) : Nat) : Int))
      ∧ (∀ i j : Fin 12, blkMat i j = ((A (blkClass i) (blkClass j) : Nat) : Int)) :=
  ⟨ambSpec, resSpec, atlSpec, frmSpec, blkSpec,
    resMat_adj, atlMat_adj, frmMat_adj, blkMat_adj⟩

/-! ## `D60`: tightness is linear in the frame indicator -/

/-- `D60`. `all_frames_fast` / `all_atlases_fast`. The tightness test is one
**affine function of the indicator**: `deg_W(v) = 24 - 4 chi_W(v)`, with no
case split on `v in W`. A candidate is therefore accepted by evaluating a
linear form at each of the `120` classes rather than by a subset search, which
is what makes the enumerations of `T10c` and `tightOK` fast. -/
@[expose] public def D60 (W : Bitset) : Prop :=
  ∀ v : K, ((D14 W v : Nat) : Int) = 24 - 4 * (if v.val ∈ W then 1 else 0)

public theorem D60_iff_D15 (W : Bitset) : D60 W ↔ D15 W := by
  rw [← T10c W]
  constructor
  · intro h v; have := h v; omega
  · intro h v; have := h v; omega

/-- The exhibited AtlasInstance passes the fast test. -/
public theorem D60_atlSet : D60 atlSet := (D60_iff_D15 atlSet).mpr (tight_of_tightOK tightComp)

/-! ## `S31`: the four-block partition is equitable -/

/-- The quotient matrix of the four-block partition: `8` on the diagonal, `0`
at the null partner of `T17`, `6` elsewhere. -/
@[expose] public def quotB (a b : Fin 4) : Nat :=
  if a = b then 8 else if b = nullPartner a then 0 else 6

public theorem equitComp :
    allFin (fun a : Fin 4 => allLt (fun v => !Bitset.mem (blkSet a) v
      || allFin (fun b : Fin 4 => decide (degN (blkSet b) v = quotB a b))) 120) = true := by
  decide +kernel

/-- The four eigenvectors of the quotient, the characters of the Klein group
the null partner generates. -/
@[expose] public def quotVec : Fin 4 → Fin 4 → Int := fun t a =>
  if t.val = 0 then 1
  else if t.val = 1 then (if a.val = 0 ∨ a.val = 3 then 1 else -1)
  else if t.val = 2 then (if a.val = 0 ∨ a.val = 2 then 1 else -1)
  else (if a.val = 0 ∨ a.val = 1 then 1 else -1)

@[expose] public def quotEig : Fin 4 → Int := fun t =>
  if t.val = 0 then 20 else if t.val = 1 then -4 else 8

/-- `S31`. The four-block partition of the AtlasInstance is equitable: every
class of `B_a` has exactly `Q[a][b]` neighbours in `B_b`. The quotient is
`B = 2I + 6J - 6M` with `M` the null-partner involution of `T17`, and its
spectrum is `{20, 8, 8, -4}`, exhibited by four pairwise orthogonal
eigenvectors. -/
public theorem S31 :
    (∀ (a : Fin 4) (v : K), v.val ∈ blkSet a → ∀ b : Fin 4,
        D14 (blkSet b) v = quotB a b)
      ∧ (∀ a b : Fin 4, (quotB a b : Int)
          = 2 * (if a = b then 1 else 0) + 6 - 6 * (if b = nullPartner a then 1 else 0))
      ∧ (∀ (t : Fin 4) (a : Fin 4),
          Vec.sum (fun b : Fin 4 => ((quotB a b : Nat) : Int) * quotVec t b)
            = quotEig t * quotVec t a)
      ∧ (∀ s t : Fin 4, s ≠ t →
          Vec.sum (fun a : Fin 4 => quotVec s a * quotVec t a) = 0)
      ∧ (∀ t : Fin 4, Vec.sum (fun a : Fin 4 => quotVec t a * quotVec t a) = 4)
      ∧ (quotEig 0 = 20 ∧ quotEig 1 = -4 ∧ quotEig 2 = 8 ∧ quotEig 3 = 8) := by
  refine ⟨fun a v hv b => ?_, by decide, by decide, by decide, by decide,
    ⟨by decide, by decide, by decide, by decide⟩⟩
  have h := allLt_true _ _ (allFin_true _ equitComp a) v.val v.isLt
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h
  have hm : Bitset.mem (blkSet a) v.val = true := hv
  rcases h with h1 | h1
  · rw [h1] at hm; exact absurd hm (by decide)
  · rw [D14_eq_degN]
    exact of_decide_eq_true (allFin_true _ h1 b)


/-! ## `S41`, `S41a`, `S41c`, `S41d`, `RC1`: the exact idempotents

`D56` and `S32` name the spectra and pin the multiplicities by traces. What
follows exhibits the projections themselves: for the AtlasInstance graph five
integer matrices `48 e_t`, read out of one relation table, and for the class
graph three combinations in the algebra `comb_mul` closes. Two finite checks
carry each system -- the projections sum to the scaled identity, and `A` acts
on each by its eigenvalue -- and everything else is algebra over `Z` and `Q`:
`e_s e_t = 0` because `A` is symmetric and the eigenvalues differ, `e_t^2 =
e_t` because the five sum to `1`.

The ranks come from split factorizations `e = B C` with `C B = 1`, whose `B`
is the echelon eigenbasis of the eigenvalue and whose `C` is the block of rows
of `e` at its pivots; that is what makes `S41c`'s `1, 2, 9, 18, 18` ranks and
not merely traces, and it identifies them with the multiplicities `atlMult`
that `S32` pins. `RC1`, the last of the twelve ambient lemmas of section 19.6,
is then read off `S41a` and `S41c` exactly as release plan section 4.4
prescribes -- through the idempotents, not through a semisimplicity theorem.

The kernel work is packed: a row of a projection is one base-`65536` numeral,
so checking `A E = lam E` costs `48` big-integer multiply-adds per row rather
than `48^2` small ones. -/

public theorem isumN_congr {f g : Nat → Int} : ∀ m, (∀ k, k < m → f k = g k) →
    isumN f m = isumN g m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ p ih =>
    intro h
    rw [isumN_succ, isumN_succ, h p (Nat.lt_succ_self p),
      ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

public theorem isumN_front (f : Nat → Int) : ∀ m,
    f 0 + isumN (fun j => f (j + 1)) m = isumN f (m + 1) := by
  intro m
  induction m with
  | zero => rfl
  | succ p ih => rw [isumN_succ, isumN_succ (f := f), ← ih]; omega

public theorem isum_eq_isumN : ∀ (m : Nat) (f : Nat → Int),
    Vec.sum (n := m) (fun k : Fin m => f k.val) = isumN f m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ p ih =>
    intro f
    show f 0 + Vec.sum (fun i : Fin p => f (Fin.succ i).val) = isumN f (p + 1)
    have h : ∀ i : Fin p, f (Fin.succ i).val = f (i.val + 1) := fun i => rfl
    rw [Vec.sum_congr h, ih (fun j => f (j + 1)), isumN_front]

public theorem isumN_add (f g : Nat → Int) : ∀ m,
    isumN (fun k => f k + g k) m = isumN f m + isumN g m := by
  intro m
  induction m with
  | zero => rfl
  | succ p ih => rw [isumN_succ, isumN_succ, isumN_succ, ih]; omega

public theorem isumN_mul_left (c : Int) (f : Nat → Int) : ∀ m,
    isumN (fun k => c * f k) m = c * isumN f m := by
  intro m
  induction m with
  | zero => show (0 : Int) = c * 0; omega
  | succ p ih => rw [isumN_succ, isumN_succ, ih, Int.mul_add]

public theorem cast_sumN (f : Nat → Nat) : ∀ m,
    ((sumN f m : Nat) : Int) = isumN (fun k => ((f k : Nat) : Int)) m := by
  intro m
  induction m with
  | zero => rfl
  | succ p ih => rw [sumN_succ, isumN_succ, ← ih]; omega

public theorem packed_rows {n : Nat} (a : Nat → Nat) (v : Nat → Nat → Nat) (w : Nat → Nat)
    (hv : ∀ j, j < n → sumN (fun k => a k * v k j) n < packBase)
    (hw : ∀ j, j < n → w j < packBase)
    (h : sumN (fun k => a k * pk packBase (v k) n) n = pk packBase w n) :
    ∀ j, j < n → sumN (fun k => a k * v k j) n = w j := by
  rw [pk_sumN packBase a v n n] at h
  exact fun j hj => pk_inj packBase (by decide) _ _ n hv hw h j hj

/-! ## The AtlasInstance scheme -/

@[expose] public def xRelTable : Nat := 4392617894329253900749627739485152876231492976963165634712079355575187451638393318606063545988837847189786078917327109793671554354393364061651044997358742284643588895623162907245461640195097385526501317515133746578929768957046675277553187852541039198616163166668286888997922195345995999257825045637476421143015439778524558532826448529496183557775342457061001290885973265075035385839971434523197166559523398954335439396554223466125014959303848637642370785168370631992970231735563001695175352570483994495956729628140532164400488179191796278761076505647325055790632182791369854625711059231781035941532189258589465804815030157881530284515364363718722099170050516818658279503747623822360490135028639098043035016214395038689716248210920022654170916809102997866292401170131251878874284957985555535171926011376728395633178246003126340304104267013887530403076108662717893516750048211411424766816634478495062532723104048695523466990315545685218292921604722228529073574337551570618507305877996002925101526961907806307879250989797430666007441744324753850600576703883633733191662204214585835023673496116587252639141997083305549782444404436825828748551815493396007265838766546226368157586508359544867136913650487211160730034303405861513583699236186195526798564022505831941677550477531952801650164999725485308364504809970179335059038712678556891000541037373588196867468726763156692055224613307289934961320357204642705498045238533336228858437420219084460735132496684695733694640423200961629902598727419474285623936131061262545039796522965058674758021546734641679242404464484033899130668717050655785980131875610527455570192119513531918179958846151933069870636339440230529874579146725668354538090284730153739268251322497239825276150203867599711248285750918959210424002124135215206981316576017585840902096519365691536567271300418811895579675193566892799839006228244024607868691793481998549594239719773371059055459661173116724005694167841977921297463941203229375134921020449734165337730217673852102028749269293030519773550491341025902612005634319554075697813583823132018722391069453744957819674502280

@[expose] public def xRelRow (i : Nat) : Nat := (xRelTable >>> (144 * i)) &&& (2 ^ 144 - 1)

@[expose] public def xRel (i j : Nat) : Nat := (xRelRow i >>> (3 * j)) &&& 7

public theorem xRel_lt (i j : Nat) : xRel i j < 8 := by
  have h : xRel i j ≤ 7 := Nat.and_le_right
  omega

@[expose] public def xValTable : Nat := 699896467034487969817087876418521447944958494804673859339420152547874393

@[expose] public def xValN (t r : Nat) : Nat := (xValTable >>> (6 * (8 * t + r))) &&& 63

public theorem xValN_le (t r : Nat) : xValN t r ≤ 63 := Nat.and_le_right

@[expose] public def xVal (t r : Nat) : Int := ((xValN t r : Nat) : Int) - 24

@[expose] public def xTgtTable : Nat := 1201545537224948318252594672165837843094057998254941447582633839692257514060125541842131905711512866219400357116956365300

@[expose] public def xTgtN (t r : Nat) : Nat := (xTgtTable >>> (10 * (8 * t + r))) &&& 1023

public theorem xTgtN_le (t r : Nat) : xTgtN t r ≤ 1023 := Nat.and_le_right

@[expose] public def xRowPk (t k : Nat) : Nat := pk packBase (fun j => xValN t (xRel k j)) 48

@[expose] public def xTgtPk (t i : Nat) : Nat := pk packBase (fun j => xTgtN t (xRel i j)) 48

public theorem xDegComp : allLt (fun i => decide (sumN (fun k => aX i k) 48 = 20)) 48 = true := by
  decide +kernel

public theorem xRelSymComp :
    allLt (fun i => allLt (fun j => decide (xRel i j = xRel j i)) 48) 48 = true := by
  decide +kernel

public theorem xSumComp :
    allLt (fun i => allLt (fun j =>
      decide (isumN (fun t => xVal t (xRel i j)) 5 = if i = j then 48 else 0)) 48) 48 = true := by
  decide +kernel

public theorem xTgtComp :
    allLt (fun t => allLt (fun r =>
      decide (((xTgtN t r : Nat) : Int) = atlLam t * xVal t r + 480)) 8) 5 = true := by
  decide

public theorem xEigComp :
    allLt (fun t => allLt (fun i =>
      decide (sumN (fun k => aX i k * xRowPk t k) 48 = xTgtPk t i)) 48) 5 = true := by
  decide +kernel

public theorem xEigN (t : Nat) (ht : t < 5) (i : Nat) (hi : i < 48) :
    ∀ j, j < 48 → sumN (fun k => aX i k * xValN t (xRel k j)) 48 = xTgtN t (xRel i j) := by
  have h := of_decide_eq_true (allLt_true _ _ (allLt_true _ _ xEigComp t ht) i hi)
  refine packed_rows (fun k => aX i k) (fun k j => xValN t (xRel k j))
    (fun j => xTgtN t (xRel i j)) ?_ ?_ h
  · intro j _
    have hb : ∀ k, aX i k * xValN t (xRel k j) ≤ 63 := by
      intro k
      have h1 : aX i k ≤ 1 := adjN_le_one _ _
      have h2 : xValN t (xRel k j) ≤ 63 := xValN_le _ _
      calc aX i k * xValN t (xRel k j) ≤ 1 * xValN t (xRel k j) :=
            Nat.mul_le_mul_right _ h1
        _ = xValN t (xRel k j) := Nat.one_mul _
        _ ≤ 63 := h2
    have hle := sumN_le_of_le (fun k => aX i k * xValN t (xRel k j)) 63 hb 48
    show _ < 65536
    omega
  · intro j _
    have := xTgtN_le t (xRel i j)
    show _ < 65536
    omega

public theorem xDeg (i : Nat) (hi : i < 48) : isumN (fun k => ((aX i k : Nat) : Int)) 48 = 20 := by
  have h : sumN (fun k => aX i k) 48 = 20 := of_decide_eq_true (allLt_true _ _ xDegComp i hi)
  rw [← cast_sumN, h]
  rfl

public theorem xEigInt (t : Nat) (ht : t < 5) (i j : Nat) (hi : i < 48) (hj : j < 48) :
    isumN (fun k => ((aX i k : Nat) : Int) * xVal t (xRel k j)) 48
      = atlLam t * xVal t (xRel i j) := by
  have hN := xEigN t ht i hi j hj
  have hcast : ((sumN (fun k => aX i k * xValN t (xRel k j)) 48 : Nat) : Int)
      = isumN (fun k => ((aX i k : Nat) : Int) * xVal t (xRel k j)) 48
        + 24 * isumN (fun k => ((aX i k : Nat) : Int)) 48 := by
    rw [cast_sumN, ← isumN_mul_left, ← isumN_add]
    refine isumN_congr 48 (fun k _ => ?_)
    have hx : ((xValN t (xRel k j) : Nat) : Int) = xVal t (xRel k j) + 24 := by
      show _ = ((xValN t (xRel k j) : Nat) : Int) - 24 + 24
      omega
    rw [Int.natCast_mul, hx, Int.mul_add]
    show _ = _ + 24 * ((aX i k : Nat) : Int)
    rw [Int.mul_comm (((aX i k : Nat) : Int)) 24]
  rw [hN, xDeg i hi] at hcast
  have htgt : ((xTgtN t (xRel i j) : Nat) : Int) = atlLam t * xVal t (xRel i j) + 480 :=
    of_decide_eq_true (allLt_true _ _ (allLt_true _ _ xTgtComp t ht) (xRel i j) (xRel_lt i j))
  rw [htgt] at hcast
  omega


/-- A verified spectral system on `n` points. -/
public structure SpecSys (nE n : Nat) where
  A : Mat n n Int
  lam : Fin nE → Int
  E : Fin nE → Mat n n Int
  sc : Int
  sc_ne : ((sc : Int) : Rat) ≠ 0
  symmA : ∀ i j, A i j = A j i
  symmE : ∀ t i j, E t i j = E t j i
  sumE : ∀ i j, Vec.sum (fun t : Fin nE => E t i j) = if i = j then sc else 0
  eig : ∀ t i j, Mat.mul A (E t) i j = lam t * E t i j
  lam_inj : ∀ s t : Fin nE, s ≠ t → lam s ≠ lam t

namespace SpecSys

variable {nE n : Nat} (S : SpecSys nE n)

public theorem eigL (t : Fin nE) (i j : Fin n) :
    Mat.mul (S.E t) S.A i j = S.lam t * S.E t i j := by
  have h : Mat.mul (S.E t) S.A i j = Mat.mul S.A (S.E t) j i := by
    show Vec.sum (fun k => S.E t i k * S.A k j) = Vec.sum (fun k => S.A j k * S.E t k i)
    refine Vec.sum_congr (fun k => ?_)
    rw [S.symmE t i k, S.symmA k j]
    exact Int.mul_comm _ _
  rw [h, S.eig t j i, S.symmE t j i]

public theorem orth {s t : Fin nE} (hst : s ≠ t) (i j : Fin n) :
    Mat.mul (S.E s) (S.E t) i j = 0 := by
  have h1 : Mat.mul (Mat.mul (S.E s) S.A) (S.E t) i j
      = S.lam s * Mat.mul (S.E s) (S.E t) i j := by
    calc Mat.mul (Mat.mul (S.E s) S.A) (S.E t) i j
        = Vec.sum (fun k => S.lam s * (S.E s i k * S.E t k j)) :=
          Vec.sum_congr (fun k => by rw [S.eigL s i k]; exact Int.mul_assoc _ _ _)
      _ = S.lam s * Mat.mul (S.E s) (S.E t) i j :=
          (Vec.mul_sum (S.lam s) (fun k => S.E s i k * S.E t k j)).symm
  have h2 : Mat.mul (S.E s) (Mat.mul S.A (S.E t)) i j
      = S.lam t * Mat.mul (S.E s) (S.E t) i j := by
    calc Mat.mul (S.E s) (Mat.mul S.A (S.E t)) i j
        = Vec.sum (fun k => S.lam t * (S.E s i k * S.E t k j)) :=
          Vec.sum_congr (fun k => by
            rw [S.eig t k j]
            show S.E s i k * (S.lam t * S.E t k j) = S.lam t * (S.E s i k * S.E t k j)
            rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm (S.E s i k) (S.lam t)])
      _ = S.lam t * Mat.mul (S.E s) (S.E t) i j :=
          (Vec.mul_sum (S.lam t) (fun k => S.E s i k * S.E t k j)).symm
  have h3 := Mat.mul_assoc_apply (S.E s) S.A (S.E t) i j
  rw [h1, h2] at h3
  have hne : S.lam s - S.lam t ≠ 0 := fun h => S.lam_inj s t hst (by omega)
  have hz : (S.lam s - S.lam t) * Mat.mul (S.E s) (S.E t) i j = 0 := by
    rw [Int.sub_mul]; omega
  rcases Int.mul_eq_zero.mp hz with h | h
  · exact absurd h hne
  · exact h

public theorem idem (t : Fin nE) (i j : Fin n) :
    Mat.mul (S.E t) (S.E t) i j = S.sc * S.E t i j := by
  have hsplit : Vec.sum (fun u : Fin nE => Mat.mul (S.E t) (S.E u) i j)
      = Mat.mul (S.E t) (S.E t) i j := by
    have h : ∀ u : Fin nE, Mat.mul (S.E t) (S.E u) i j
        = if t = u then Mat.mul (S.E t) (S.E t) i j else 0 := by
      intro u
      by_cases hu : t = u
      · rw [if_pos hu, hu]
      · rw [if_neg hu]; exact S.orth hu i j
    rw [Vec.sum_congr h]
    exact Vec.sum_ite_eq t (fun _ => Mat.mul (S.E t) (S.E t) i j)
  have hex : Vec.sum (fun u : Fin nE => Mat.mul (S.E t) (S.E u) i j) = S.sc * S.E t i j := by
    calc Vec.sum (fun u : Fin nE => Mat.mul (S.E t) (S.E u) i j)
        = Vec.sum (fun k : Fin n => Vec.sum (fun u : Fin nE => S.E t i k * S.E u k j)) :=
          Vec.sum_exchange (fun (u : Fin nE) (k : Fin n) => S.E t i k * S.E u k j)
      _ = Vec.sum (fun k : Fin n => S.E t i k * Vec.sum (fun u : Fin nE => S.E u k j)) :=
          Vec.sum_congr (fun k => (Vec.mul_sum (S.E t i k) (fun u : Fin nE => S.E u k j)).symm)
      _ = Vec.sum (fun k : Fin n => if k = j then S.E t i k * S.sc else 0) :=
          Vec.sum_congr (fun k => by
            rw [S.sumE k j]
            by_cases hk : k = j
            · rw [if_pos hk, if_pos hk]
            · rw [if_neg hk, if_neg hk]; exact Int.mul_zero _)
      _ = S.E t i j * S.sc := Vec.sum_ite_eq' j (fun k => S.E t i k * S.sc)
      _ = S.sc * S.E t i j := Int.mul_comm _ _
  rw [← hsplit, hex]

public theorem decomp (i j : Fin n) :
    Vec.sum (fun t : Fin nE => S.lam t * S.E t i j) = S.sc * S.A i j := by
  calc Vec.sum (fun t : Fin nE => S.lam t * S.E t i j)
      = Vec.sum (fun t : Fin nE => Mat.mul S.A (S.E t) i j) :=
        Vec.sum_congr (fun t => (S.eig t i j).symm)
    _ = Vec.sum (fun k : Fin n => Vec.sum (fun t : Fin nE => S.A i k * S.E t k j)) :=
        Vec.sum_exchange (fun (t : Fin nE) (k : Fin n) => S.A i k * S.E t k j)
    _ = Vec.sum (fun k : Fin n => S.A i k * Vec.sum (fun t : Fin nE => S.E t k j)) :=
        Vec.sum_congr (fun k => (Vec.mul_sum (S.A i k) (fun t : Fin nE => S.E t k j)).symm)
    _ = Vec.sum (fun k : Fin n => if k = j then S.A i k * S.sc else 0) :=
        Vec.sum_congr (fun k => by
          rw [S.sumE k j]
          by_cases hk : k = j
          · rw [if_pos hk, if_pos hk]
          · rw [if_neg hk, if_neg hk]; exact Int.mul_zero _)
    _ = S.A i j * S.sc := Vec.sum_ite_eq' j (fun k => S.A i k * S.sc)
    _ = S.sc * S.A i j := Int.mul_comm _ _

end SpecSys



/-! ### The projections as rational idempotents -/

public theorem mul4 {α : Type} [CommRing α] (a b q : α) :
    CommRing.mul (CommRing.mul a q) (CommRing.mul b q)
      = CommRing.mul (CommRing.mul a b) (CommRing.mul q q) := by
  rw [CommRing.mul_assoc, ← CommRing.mul_assoc q b q, CommRing.mul_comm q b,
    CommRing.mul_assoc b q q, ← CommRing.mul_assoc]

public theorem qsum_cast' {m : Nat} (f : Fin m → Int) (k : Rat) :
    Vec.sum (fun c : Fin m => ((f c : Int) : Rat) * k) = ((Vec.sum f : Int) : Rat) * k := by
  have h1 : Vec.sum (fun c : Fin m => ((f c : Int) : Rat) * k)
      = Vec.sum (fun c : Fin m => ((f c : Int) : Rat)) * k :=
    (Vec.sum_mul (fun c : Fin m => ((f c : Int) : Rat)) k).symm
  have h2 : Vec.sum (fun c : Fin m => ((f c : Int) : Rat)) = ((Vec.sum f : Int) : Rat) :=
    (hom_map_sum intToRat f).symm
  rw [h1, h2]


namespace SpecSys

variable {nE n : Nat} (S : SpecSys nE n)

/-- The scale, in `Q`. -/
@[expose] public def q : Rat := ((S.sc : Int) : Rat)

/-- The genuine idempotent: the integer projection divided by the scale. -/
@[expose] public def e (t : Fin nE) : Mat n n Rat :=
  fun i j => ((S.E t i j : Int) : Rat) * S.q⁻¹

public theorem q_inv_cancel : S.q * S.q⁻¹ = 1 := Rat.mul_inv_cancel S.q S.sc_ne

public theorem e_mul (s t : Fin nE) (i j : Fin n) :
    Mat.mul (S.e s) (S.e t) i j
      = ((Mat.mul (S.E s) (S.E t) i j : Int) : Rat) * (S.q⁻¹ * S.q⁻¹) := by
  have hstep : ∀ k : Fin n, S.e s i k * S.e t k j
      = ((S.E s i k * S.E t k j : Int) : Rat) * (S.q⁻¹ * S.q⁻¹) := by
    intro k
    show (((S.E s i k : Int) : Rat) * S.q⁻¹) * (((S.E t k j : Int) : Rat) * S.q⁻¹) = _
    rw [Rat.intCast_mul]
    exact mul4 (((S.E s i k : Int) : Rat)) (((S.E t k j : Int) : Rat)) S.q⁻¹
  calc Mat.mul (S.e s) (S.e t) i j
      = Vec.sum (fun k => ((S.E s i k * S.E t k j : Int) : Rat) * (S.q⁻¹ * S.q⁻¹)) :=
        Vec.sum_congr hstep
    _ = Vec.sum (fun k => ((S.E s i k * S.E t k j : Int) : Rat)) * (S.q⁻¹ * S.q⁻¹) :=
        (Vec.sum_mul _ _).symm
    _ = ((Mat.mul (S.E s) (S.E t) i j : Int) : Rat) * (S.q⁻¹ * S.q⁻¹) := by
        have h : ((Mat.mul (S.E s) (S.E t) i j : Int) : Rat)
            = Vec.sum (fun k => ((S.E s i k * S.E t k j : Int) : Rat)) :=
          hom_map_sum intToRat (fun k => S.E s i k * S.E t k j)
        rw [h]

/-- `e_s e_t = 0` for distinct eigenvalues. -/
public theorem e_orth {s t : Fin nE} (hst : s ≠ t) (i j : Fin n) :
    Mat.mul (S.e s) (S.e t) i j = 0 := by
  rw [S.e_mul s t i j, S.orth hst i j]
  show ((0 : Int) : Rat) * _ = 0
  rw [Rat.intCast_zero]
  exact Rat.zero_mul _

/-- `e_t e_t = e_t`: the projections are idempotent on the nose. -/
public theorem e_idem (t : Fin nE) (i j : Fin n) :
    Mat.mul (S.e t) (S.e t) i j = S.e t i j := by
  rw [S.e_mul t t i j, S.idem t i j, Rat.intCast_mul]
  show (S.q * ((S.E t i j : Int) : Rat)) * (S.q⁻¹ * S.q⁻¹) = ((S.E t i j : Int) : Rat) * S.q⁻¹
  rw [Rat.mul_comm S.q (((S.E t i j : Int) : Rat)), Rat.mul_assoc,
    ← Rat.mul_assoc S.q S.q⁻¹ S.q⁻¹, S.q_inv_cancel, Rat.one_mul]

/-- The projections sum to the identity. -/
public theorem e_sum (i j : Fin n) :
    Vec.sum (fun t : Fin nE => S.e t i j) = (Mat.id : Mat n n Rat) i j := by
  have h1 : Vec.sum (fun t : Fin nE => S.e t i j)
      = Vec.sum (fun t : Fin nE => ((S.E t i j : Int) : Rat)) * S.q⁻¹ :=
    (Vec.sum_mul (fun t : Fin nE => ((S.E t i j : Int) : Rat)) S.q⁻¹).symm
  have h2 : Vec.sum (fun t : Fin nE => ((S.E t i j : Int) : Rat))
      = ((Vec.sum (fun t : Fin nE => S.E t i j) : Int) : Rat) :=
    (hom_map_sum intToRat (fun t : Fin nE => S.E t i j)).symm
  rw [h1, h2, S.sumE i j]
  by_cases hij : i = j
  · rw [if_pos hij]
    show S.q * S.q⁻¹ = if i = j then (1 : Rat) else 0
    rw [S.q_inv_cancel, if_pos hij]
  · rw [if_neg hij]
    show ((0 : Int) : Rat) * S.q⁻¹ = if i = j then (1 : Rat) else 0
    rw [Rat.intCast_zero, Rat.zero_mul, if_neg hij]

end SpecSys


/-! ### The AtlasInstance graph as a spectral system -/

/-- The five eigenprojections of the AtlasInstance graph, scaled by `48`. -/
@[expose] public def xEm (t : Fin 5) : Mat 48 48 Int := fun i j => xVal t.val (xRel i.val j.val)

/-- The five eigenvalues `20, 8, 4, 0, -4`. -/
@[expose] public def xLam (t : Fin 5) : Int := atlLam t.val

public def xSpec : SpecSys 5 48 where
  A := atlMat
  lam := xLam
  E := xEm
  sc := 48
  sc_ne := by decide
  symmA := by
    intro i j
    rw [atlMat_adj i j, atlMat_adj j i]
    show ((A (xClass i) (xClass j) : Nat) : Int) = ((A (xClass j) (xClass i) : Nat) : Int)
    rw [A_comm]
  symmE := by
    intro t i j
    show xVal t.val (xRel i.val j.val) = xVal t.val (xRel j.val i.val)
    rw [of_decide_eq_true (allLt_true _ _ (allLt_true _ _ xRelSymComp i.val i.isLt) j.val j.isLt)]
  sumE := by
    intro i j
    show Vec.sum (fun t : Fin 5 => xVal t.val (xRel i.val j.val)) = _
    rw [isum_eq_isumN 5 (fun t => xVal t (xRel i.val j.val)),
      of_decide_eq_true (allLt_true _ _ (allLt_true _ _ xSumComp i.val i.isLt) j.val j.isLt)]
    by_cases hij : i = j
    · rw [if_pos (congrArg Fin.val hij), if_pos hij]
    · rw [if_neg (fun h => hij (Fin.eq_of_val_eq h)), if_neg hij]
  eig := by
    intro t i j
    have hterm : ∀ k : Fin 48, atlMat i k * xEm t k j
        = (fun c => ((aX i.val c : Nat) : Int) * xVal t.val (xRel c j.val)) k.val := by
      intro k
      rw [atlMat_adj i k]
      show ((AX i k : Nat) : Int) * xVal t.val (xRel k.val j.val) = _
      rw [AX_eq_aX]
    show Vec.sum (fun k : Fin 48 => atlMat i k * xEm t k j) = _
    rw [Vec.sum_congr hterm,
      isum_eq_isumN 48 (fun c => ((aX i.val c : Nat) : Int) * xVal t.val (xRel c j.val)),
      xEigInt t.val t.isLt i.val j.val i.isLt j.isLt]
    rfl
  lam_inj := by decide


/-! ### Rank certificates -/

/-- `M` has rank `r`: it factors through `r`, and the factorization is split.
`M = B C` forces `rank M <= r`; `C B = 1` forces `rank M >= r`, because then
`B = B (C B) = (B C) B = M B` puts the `r` columns of `B` -- independent, since
`C` is a left inverse -- inside the image of `M`. Neither half alone pins the
rank, and neither half needs a determinant, a basis or a dimension theory. -/
@[expose] public def HasMatRank {n : Nat} (M : Mat n n Rat) (r : Nat) : Prop :=
  ∃ (B : Mat n r Rat) (C : Mat r n Rat),
    (∀ i j, Mat.mul B C i j = M i j) ∧ (∀ c d, Mat.mul C B c d = (Mat.id : Mat r r Rat) c d)

/-- Where eigenvalue `t`'s block of certificate columns begins. -/
@[expose] public def xColBase : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 12
  | _ => 30

/-- The denominator each certificate carries: the common denominator of the
echelon eigenbasis of eigenvalue `t`, cleared. -/
@[expose] public def xDen : Nat → Int
  | 4 => 2
  | _ => 1

/-- The pivot coordinates of the echelon eigenbasis: seven bits per column. -/
@[expose] public def xFreeTable : Nat := 51796440500452569243473516164296917347754394170300389654891859478730218712977335139296529319927205807

@[expose] public def xFree (t c : Nat) : Nat := (xFreeTable >>> (7 * (xColBase t + c))) &&& 127

/-- The echelon eigenbases themselves, four bits per entry, biased by `4`:
column `c` of eigenvalue `t` in coordinate `i`. -/
@[expose] public def xBTable : Nat := 76799191956643679787012178503198414200419569675847589974491204813021386700092156070956938145440284695937074582429877039881982351195464370091137511845096849718029505473478698118962823330868771761581103269321131629904520706714492583125080333083144547754649003520069648720941928669120446358785284530778247547739038158889963392102565032769668507255408255436270366818876209364339181220579823704162785546824658532563334783793940750471376959969482880550156370451045142616898015929209165127669854525467379232123354522253407744074746308067958928944601332069691222927910959814525907764420561812266394589829784455560301593524997310342479285472854099436182571354795421632151670353147300583857143782167839938478420393351555319542561421337005721040442118189361424738482623791450350906507691891308507333410655269517140963097621207919688565379702264516342876075439710527819384660647358273119125930578023461487729683048467742764397831366866927012635264657601651501360406525077703540013654337272475746291460942306080950683181695938711139990469204229097458802548480624150929551561530902145067618718058374441918820598747247629145095411805630159133607056103666097457186235876710321671320998826928565598684033360143217867174403523160415748134947107212466386669065961173541045767611187117514567969710321267192262773311475671521410725766685254699427506445991890878682890781120406338054100721195674960662803681653489300743119972775679367629698542493311441319237942732407101802033075401843587215923126982358177144531883099240945411639344623003595287391048847380758405807545213250559084848021653164905431972821829579730081880600608800400511313844872983026448184691957777892832098291293562648764572825493331702650702524288509475431959019468980564328867418862987158295538201506973181232050451727158959015037381963768567782557648174932324004816291513961352704866816394725442489020649402761685194317376258584238437272766685991068273191167593790780770511935205054498990086249747258433855875998764668801672646147622295962498749988541618856893745376528153844190967844769726284513304119342938053411675828498589923616239887821620006238122639572906087906211835725877038047097664626558521348601338882185142202446970443578606733455008939338883513808442360954677653911191797473316304607108955616246876343041127533844354465648618015052728299956198231919497011939744066490082566405800971289172627153478915450700874005361576539574093746125543054635968124370600755913761660635904126794423293980354557311086422820267052646756402237640342231665576586078351996770043873749074246428745623796017122745455979837167685204831125411417812686678542940681112667294221133399363167724432445742682947282423301423810956021194037972535865620423044474880827748986555690598031910820559252593411728678643477719557799419428687121323742549

@[expose] public def xBN (t c i : Nat) : Nat :=
  (xBTable >>> (4 * (48 * (xColBase t + c) + i))) &&& 15

@[expose] public def xB (t c i : Nat) : Int := ((xBN t c i : Nat) : Int) - 4

/-- The image half of the certificate: `B` spans the image of the projection,
`B * (rows of E at the pivots) = d * E`. -/
public theorem xImgComp :
    allLt (fun t => allLt (fun i => allLt (fun j =>
      decide (isumN (fun c => xB t c i * xVal t (xRel (xFree t c) j)) (atlMult t)
        = xDen t * xVal t (xRel i j))) 48) 48) 5 = true := by
  decide +kernel

/-- The split half of the certificate: the pivot rows of `E` invert `B`. -/
public theorem xSplitComp :
    allLt (fun t => allLt (fun c => allLt (fun d =>
      decide (isumN (fun j => xVal t (xRel (xFree t c) j) * xB t d j) 48
        = if c = d then 48 * xDen t else 0)) (atlMult t)) (atlMult t)) 5 = true := by
  decide +kernel


/-! ### Rank from an integer certificate -/

/-- A split factorization assembled from integer data: `B` spans the image of
`E`, `P` is a block of rows of `E` that inverts `B` up to the scale `sc * d`,
and `M` is `E / sc`. This is the one lemma both spectral systems reach `S41c`
through; nothing in it is specific to a graph. -/
public theorem hasRank_of_cert {n m : Nat} (M : Mat n n Rat) (E : Mat n n Int)
    (B : Mat n m Int) (P : Mat m n Int) (sc d : Int)
    (hM : ∀ i j, M i j = ((E i j : Int) : Rat) * ((sc : Int) : Rat)⁻¹)
    (hne : (((sc * d : Int)) : Rat) ≠ 0)
    (hd : ((d : Int) : Rat) * (((sc * d : Int)) : Rat)⁻¹ = ((sc : Int) : Rat)⁻¹)
    (himg : ∀ i j : Fin n, Vec.sum (fun c : Fin m => B i c * P c j) = d * E i j)
    (hsplit : ∀ c e : Fin m, Vec.sum (fun j : Fin n => P c j * B j e)
      = if c = e then sc * d else 0) :
    HasMatRank M m := by
  refine ⟨fun i c => ((B i c : Int) : Rat),
    fun c j => ((P c j : Int) : Rat) * (((sc * d : Int)) : Rat)⁻¹, ?_, ?_⟩
  · intro i j
    have hterm : ∀ c : Fin m,
        CommRing.mul (((B i c : Int) : Rat))
            (((P c j : Int) : Rat) * (((sc * d : Int)) : Rat)⁻¹)
          = (((fun c : Fin m => B i c * P c j) c : Int) : Rat)
            * (((sc * d : Int)) : Rat)⁻¹ := by
      intro c
      have hc : ((B i c * P c j : Int) : Rat)
          = ((B i c : Int) : Rat) * ((P c j : Int) : Rat) := Rat.intCast_mul _ _
      show ((B i c : Int) : Rat)
          * (((P c j : Int) : Rat) * (((sc * d : Int)) : Rat)⁻¹) = _
      rw [hc, Rat.mul_assoc]
    have hcast : ((d * E i j : Int) : Rat) = ((d : Int) : Rat) * ((E i j : Int) : Rat) :=
      Rat.intCast_mul _ _
    calc Mat.mul (fun i c => ((B i c : Int) : Rat))
          (fun c j => ((P c j : Int) : Rat) * (((sc * d : Int)) : Rat)⁻¹) i j
        = Vec.sum (fun c : Fin m =>
            (((fun c : Fin m => B i c * P c j) c : Int) : Rat)
              * (((sc * d : Int)) : Rat)⁻¹) := Vec.sum_congr hterm
      _ = ((Vec.sum (fun c : Fin m => B i c * P c j) : Int) : Rat)
            * (((sc * d : Int)) : Rat)⁻¹ :=
          qsum_cast' (fun c : Fin m => B i c * P c j) ((((sc * d : Int)) : Rat)⁻¹)
      _ = (((d : Int) : Rat) * ((E i j : Int) : Rat)) * (((sc * d : Int)) : Rat)⁻¹ := by
          rw [himg i j, hcast]
      _ = ((E i j : Int) : Rat) * (((d : Int) : Rat) * (((sc * d : Int)) : Rat)⁻¹) := by
          rw [Rat.mul_comm (((d : Int) : Rat)) _, Rat.mul_assoc]
      _ = M i j := by rw [hd, hM i j]
  · intro c e
    have hterm : ∀ j : Fin n,
        CommRing.mul (((P c j : Int) : Rat) * (((sc * d : Int)) : Rat)⁻¹)
            (((B j e : Int) : Rat))
          = (((fun j : Fin n => P c j * B j e) j : Int) : Rat)
            * (((sc * d : Int)) : Rat)⁻¹ := by
      intro j
      have hc : ((P c j * B j e : Int) : Rat)
          = ((P c j : Int) : Rat) * ((B j e : Int) : Rat) := Rat.intCast_mul _ _
      show (((P c j : Int) : Rat) * (((sc * d : Int)) : Rat)⁻¹) * ((B j e : Int) : Rat) = _
      rw [hc, Rat.mul_assoc, Rat.mul_comm ((((sc * d : Int)) : Rat)⁻¹) (((B j e : Int) : Rat)),
        ← Rat.mul_assoc]
    have hmain : Mat.mul (fun c j => ((P c j : Int) : Rat) * (((sc * d : Int)) : Rat)⁻¹)
        (fun i c => ((B i c : Int) : Rat)) c e
        = ((if c = e then (sc * d : Int) else 0 : Int) : Rat)
          * (((sc * d : Int)) : Rat)⁻¹ := by
      calc Mat.mul (fun c j => ((P c j : Int) : Rat) * (((sc * d : Int)) : Rat)⁻¹)
            (fun i c => ((B i c : Int) : Rat)) c e
          = Vec.sum (fun j : Fin n =>
              (((fun j : Fin n => P c j * B j e) j : Int) : Rat)
                * (((sc * d : Int)) : Rat)⁻¹) := Vec.sum_congr hterm
        _ = ((Vec.sum (fun j : Fin n => P c j * B j e) : Int) : Rat)
              * (((sc * d : Int)) : Rat)⁻¹ :=
            qsum_cast' (fun j : Fin n => P c j * B j e) ((((sc * d : Int)) : Rat)⁻¹)
        _ = _ := by rw [hsplit c e]
    rw [hmain]
    by_cases hce : c = e
    · rw [if_pos hce, Rat.mul_inv_cancel _ hne]
      show (1 : Rat) = if c = e then (1 : Rat) else 0
      rw [if_pos hce]
    · rw [if_neg hce, Rat.intCast_zero, Rat.zero_mul]
      show (0 : Rat) = if c = e then (1 : Rat) else 0
      rw [if_neg hce]


public theorem xDenComp :
    allLt (fun t => decide (((xDen t : Int) : Rat) * (((48 * xDen t : Int)) : Rat)⁻¹
      = (((48 : Int)) : Rat)⁻¹) && decide (¬ ((((48 * xDen t : Int)) : Rat) = 0))) 5 = true := by
  decide +kernel

public theorem xDenId (t : Nat) (ht : t < 5) :
    ((xDen t : Int) : Rat) * (((48 * xDen t : Int)) : Rat)⁻¹ = (((48 : Int)) : Rat)⁻¹ :=
  of_decide_eq_true (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ xDenComp t ht)).1

public theorem xDenNe (t : Nat) (ht : t < 5) : (((48 * xDen t : Int)) : Rat) ≠ 0 :=
  of_decide_eq_true (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ xDenComp t ht)).2

/-- The rank of each projection of the AtlasInstance graph: the certificate is
the echelon eigenbasis of the eigenvalue, against the pivot rows of the
projection itself. -/
public theorem xHasRank (t : Fin 5) : HasMatRank (xSpec.e t) (atlMult t.val) := by
  refine hasRank_of_cert (xSpec.e t) (xEm t)
    (fun (i : Fin 48) (c : Fin (atlMult t.val)) => xB t.val c.val i.val)
    (fun (c : Fin (atlMult t.val)) (j : Fin 48) =>
      xVal t.val (xRel (xFree t.val c.val) j.val))
    48 (xDen t.val) (fun _ _ => rfl) (xDenNe t.val t.isLt) (xDenId t.val t.isLt)
    (fun i j => ?_) (fun c e => ?_)
  · have himg : isumN (fun c => xB t.val c i.val * xVal t.val (xRel (xFree t.val c) j.val))
        (atlMult t.val) = xDen t.val * xVal t.val (xRel i.val j.val) :=
      of_decide_eq_true (allLt_true _ _ (allLt_true _ _
        (allLt_true _ _ xImgComp t.val t.isLt) i.val i.isLt) j.val j.isLt)
    rw [isum_eq_isumN (atlMult t.val)
      (fun c => xB t.val c i.val * xVal t.val (xRel (xFree t.val c) j.val))]
    exact himg
  · have hsplit : isumN (fun j => xVal t.val (xRel (xFree t.val c.val) j) * xB t.val e.val j) 48
        = if c.val = e.val then 48 * xDen t.val else 0 :=
      of_decide_eq_true (allLt_true _ _ (allLt_true _ _
        (allLt_true _ _ xSplitComp t.val t.isLt) c.val c.isLt) e.val e.isLt)
    rw [isum_eq_isumN 48
      (fun j => xVal t.val (xRel (xFree t.val c.val) j) * xB t.val e.val j), hsplit]
    by_cases hce : c = e
    · rw [if_pos (congrArg Fin.val hce), if_pos hce]
    · rw [if_neg (fun h => hce (Fin.eq_of_val_eq h)), if_neg hce]


/-! ### Traces, powers and the annihilating polynomial -/

public theorem nsmul_one_rat : ∀ n : Nat, nsmul n (1 : Rat) = ((n : Nat) : Rat) := by
  intro n
  induction n with
  | zero => rfl
  | succ p ih =>
    show (1 : Rat) + nsmul p (1 : Rat) = _
    rw [ih]
    push_cast
    exact Rat.add_comm _ _

/-- The trace of a matrix with a split factorization is its rank: `tr(BC) =
tr(CB) = tr(1_r) = r`. -/
public theorem trace_hasRank {n r : Nat} {M : Mat n n Rat} (h : HasMatRank M r) :
    Vec.sum (fun i : Fin n => M i i) = ((r : Nat) : Rat) := by
  obtain ⟨B, C, hBC, hCB⟩ := h
  have h1 : Vec.sum (fun i : Fin n => M i i)
      = Vec.sum (fun i : Fin n => Vec.sum (fun c : Fin r => CommRing.mul (B i c) (C c i))) :=
    Vec.sum_congr (fun i => (hBC i i).symm)
  have h2 : Vec.sum (fun i : Fin n => Vec.sum (fun c : Fin r => CommRing.mul (B i c) (C c i)))
      = Vec.sum (fun c : Fin r => Vec.sum (fun i : Fin n => CommRing.mul (C c i) (B i c))) := by
    rw [Vec.sum_exchange (fun (i : Fin n) (c : Fin r) => CommRing.mul (B i c) (C c i))]
    exact Vec.sum_congr (fun c => Vec.sum_congr (fun i => CommRing.mul_comm _ _))
  have h3 : Vec.sum (fun c : Fin r => Vec.sum (fun i : Fin n => CommRing.mul (C c i) (B i c)))
      = Vec.sum (fun _ : Fin r => (1 : Rat)) := by
    refine Vec.sum_congr (fun c => ?_)
    have hc : Mat.mul C B c c = (Mat.id : Mat r r Rat) c c := hCB c c
    show Mat.mul C B c c = (1 : Rat)
    rw [hc]
    show (if c = c then (1 : Rat) else 0) = 1
    rw [if_pos rfl]
  rw [h1, h2, h3, Vec.sum_const, nsmul_one_rat]

/-- Powers of an integer matrix. -/
@[expose] public def matPow {n : Nat} (M : Mat n n Int) : Nat → Mat n n Int
  | 0 => Mat.id
  | p + 1 => Mat.mul M (matPow M p)

namespace SpecSys

variable {nE n : Nat} (S : SpecSys nE n)

/-- Every power of `A` acts on the `t`-th projection by `lam t ^ p`. -/
public theorem pow_eig (t : Fin nE) : ∀ (p : Nat) (i j : Fin n),
    Mat.mul (matPow S.A p) (S.E t) i j = S.lam t ^ p * S.E t i j := by
  intro p
  induction p with
  | zero =>
    intro i j
    show Mat.mul (Mat.id : Mat n n Int) (S.E t) i j = S.lam t ^ 0 * S.E t i j
    rw [Mat.id_mul_apply, Int.pow_zero, Int.one_mul]
  | succ p ih =>
    intro i j
    have hterm : ∀ k : Fin n, CommRing.mul (S.A i k) (Mat.mul (matPow S.A p) (S.E t) k j)
        = CommRing.mul (S.lam t ^ p) (CommRing.mul (S.A i k) (S.E t k j)) := by
      intro k
      show S.A i k * Mat.mul (matPow S.A p) (S.E t) k j = _
      rw [ih k j]
      show S.A i k * (S.lam t ^ p * S.E t k j) = S.lam t ^ p * (S.A i k * S.E t k j)
      rw [← Int.mul_assoc, Int.mul_comm (S.A i k) (S.lam t ^ p), Int.mul_assoc]
    show Mat.mul (Mat.mul S.A (matPow S.A p)) (S.E t) i j = _
    rw [Mat.mul_assoc_apply S.A (matPow S.A p) (S.E t) i j]
    show Vec.sum (fun k => CommRing.mul (S.A i k) (Mat.mul (matPow S.A p) (S.E t) k j)) = _
    rw [Vec.sum_congr hterm, ← Vec.mul_sum]
    show S.lam t ^ p * Mat.mul S.A (S.E t) i j = _
    rw [S.eig t i j, ← Int.mul_assoc, Int.pow_succ, Int.mul_comm (S.lam t ^ p) (S.lam t)]

/-- Against any matrix the projections sum to the scaled identity: this is the
one step every argument below takes to get from the five pieces back to the
whole. -/
public theorem mul_sumE (P : Mat n n Int) (i j : Fin n) :
    Vec.sum (fun t : Fin nE => Mat.mul P (S.E t) i j) = P i j * S.sc := by
  calc Vec.sum (fun t : Fin nE => Mat.mul P (S.E t) i j)
      = Vec.sum (fun k : Fin n => Vec.sum (fun t : Fin nE =>
          CommRing.mul (P i k) (S.E t k j))) :=
        Vec.sum_exchange
          (fun (t : Fin nE) (k : Fin n) => CommRing.mul (P i k) (S.E t k j))
    _ = Vec.sum (fun k : Fin n => CommRing.mul (P i k)
          (Vec.sum (fun t : Fin nE => S.E t k j))) :=
        Vec.sum_congr (fun k => (Vec.mul_sum _ _).symm)
    _ = Vec.sum (fun k : Fin n => if k = j then P i k * S.sc else 0) :=
        Vec.sum_congr (fun k => by
          show P i k * Vec.sum (fun t : Fin nE => S.E t k j) = _
          rw [S.sumE k j]
          by_cases hk : k = j
          · rw [if_pos hk, if_pos hk]
          · rw [if_neg hk, if_neg hk]; exact Int.mul_zero _)
    _ = P i j * S.sc := Vec.sum_ite_eq' j (fun k => P i k * S.sc)

/-- The trace of every power, against the traces of the projections. -/
public theorem trace_pow (p : Nat) :
    Vec.sum (fun t : Fin nE => S.lam t ^ p * Vec.sum (fun i : Fin n => S.E t i i))
      = Vec.sum (fun i : Fin n => matPow S.A p i i) * S.sc := by
  calc Vec.sum (fun t : Fin nE => S.lam t ^ p * Vec.sum (fun i : Fin n => S.E t i i))
      = Vec.sum (fun t : Fin nE => Vec.sum (fun i : Fin n => S.lam t ^ p * S.E t i i)) :=
        Vec.sum_congr (fun t => Vec.mul_sum _ _)
    _ = Vec.sum (fun i : Fin n => Vec.sum (fun t : Fin nE => S.lam t ^ p * S.E t i i)) :=
        Vec.sum_exchange (fun (t : Fin nE) (i : Fin n) => S.lam t ^ p * S.E t i i)
    _ = Vec.sum (fun i : Fin n => Vec.sum (fun t : Fin nE =>
          Mat.mul (matPow S.A p) (S.E t) i i)) :=
        Vec.sum_congr (fun i => Vec.sum_congr (fun t => (S.pow_eig t p i i).symm))
    _ = Vec.sum (fun i : Fin n => matPow S.A p i i * S.sc) :=
        Vec.sum_congr (fun i => S.mul_sumE (matPow S.A p) i i)
    _ = Vec.sum (fun i : Fin n => matPow S.A p i i) * S.sc :=
        (Vec.sum_mul (fun i : Fin n => matPow S.A p i i) S.sc).symm

end SpecSys


/-! ### The rational form of a spectral system -/

namespace SpecSys

variable {nE n : Nat} (S : SpecSys nE n)

/-- The graph over `Q`. -/
@[expose] public def Aq : Mat n n Rat := Mat.map intToRat S.A

/-- Each rational projection is a projection onto an eigenspace. -/
public theorem e_eig (t : Fin nE) (i j : Fin n) :
    Mat.mul S.Aq (S.e t) i j = ((S.lam t : Int) : Rat) * S.e t i j := by
  have hterm : ∀ k : Fin n, CommRing.mul (S.Aq i k) (S.e t k j)
      = (((fun k : Fin n => S.A i k * S.E t k j) k : Int) : Rat) * S.q⁻¹ := by
    intro k
    have hc : ((S.A i k * S.E t k j : Int) : Rat)
        = ((S.A i k : Int) : Rat) * ((S.E t k j : Int) : Rat) := Rat.intCast_mul _ _
    show ((S.A i k : Int) : Rat) * (((S.E t k j : Int) : Rat) * S.q⁻¹) = _
    rw [hc, Rat.mul_assoc]
  have hstep : Mat.mul S.Aq (S.e t) i j
      = ((Vec.sum (fun k : Fin n => S.A i k * S.E t k j) : Int) : Rat) * S.q⁻¹ := by
    calc Mat.mul S.Aq (S.e t) i j
        = Vec.sum (fun k : Fin n => CommRing.mul (S.Aq i k) (S.e t k j)) := rfl
      _ = Vec.sum (fun k : Fin n =>
            (((fun k : Fin n => S.A i k * S.E t k j) k : Int) : Rat) * S.q⁻¹) :=
          Vec.sum_congr hterm
      _ = _ := qsum_cast' (fun k : Fin n => S.A i k * S.E t k j) S.q⁻¹
  have heig : Vec.sum (fun k : Fin n => S.A i k * S.E t k j) = S.lam t * S.E t i j := S.eig t i j
  rw [hstep, heig, Rat.intCast_mul]
  show (((S.lam t : Int) : Rat) * ((S.E t i j : Int) : Rat)) * S.q⁻¹ = _
  rw [Rat.mul_assoc]
  rfl

/-- The spectral decomposition: `A` is the eigenvalue-weighted sum of its
projections. -/
public theorem e_decomp (i j : Fin n) :
    Vec.sum (fun t : Fin nE => ((S.lam t : Int) : Rat) * S.e t i j) = ((S.A i j : Int) : Rat) := by
  have hterm : ∀ t : Fin nE, ((S.lam t : Int) : Rat) * S.e t i j
      = (((fun t : Fin nE => S.lam t * S.E t i j) t : Int) : Rat) * S.q⁻¹ := by
    intro t
    have hc : ((S.lam t * S.E t i j : Int) : Rat)
        = ((S.lam t : Int) : Rat) * ((S.E t i j : Int) : Rat) := Rat.intCast_mul _ _
    show ((S.lam t : Int) : Rat) * (((S.E t i j : Int) : Rat) * S.q⁻¹) = _
    rw [hc, Rat.mul_assoc]
  rw [Vec.sum_congr hterm, qsum_cast' (fun t : Fin nE => S.lam t * S.E t i j) S.q⁻¹, S.decomp i j,
    Rat.intCast_mul]
  show S.q * ((S.A i j : Int) : Rat) * S.q⁻¹ = _
  rw [Rat.mul_comm S.q (((S.A i j : Int) : Rat)), Rat.mul_assoc, S.q_inv_cancel, Rat.mul_one]

/-- The trace of a projection, from its rank. -/
public theorem trace_E_of_rank (t : Fin nE) (r : Nat) (h : HasMatRank (S.e t) r) :
    Vec.sum (fun i : Fin n => S.E t i i) = S.sc * ((r : Nat) : Int) := by
  have h1 : Vec.sum (fun i : Fin n => S.e t i i) = ((r : Nat) : Rat) := trace_hasRank h
  have h2 : Vec.sum (fun i : Fin n => S.e t i i)
      = ((Vec.sum (fun i : Fin n => S.E t i i) : Int) : Rat) * S.q⁻¹ :=
    qsum_cast' (fun i : Fin n => S.E t i i) S.q⁻¹
  rw [h2] at h1
  have h3 : ((Vec.sum (fun i : Fin n => S.E t i i) : Int) : Rat) * S.q⁻¹ * S.q
      = ((r : Nat) : Rat) * S.q := by rw [h1]
  rw [Rat.mul_assoc, Rat.mul_comm S.q⁻¹ S.q, S.q_inv_cancel, Rat.mul_one] at h3
  have hrr : ((((r : Nat) : Int)) : Rat) = ((r : Nat) : Rat) := by norm_cast
  have h4 : ((S.sc * ((r : Nat) : Int) : Int) : Rat) = ((r : Nat) : Rat) * S.q := by
    rw [Rat.intCast_mul, hrr]
    exact Rat.mul_comm _ _
  rw [← h4] at h3
  exact Rat.intCast_inj.mp h3

end SpecSys


/-! ### `RC1`: the decomposition of the module -/

public theorem apply_sum {n m : Nat} (M : Mat n n Rat) (y : Fin m → Vec n Rat) (i : Fin n) :
    Mat.apply M (fun j => Vec.sum (fun s : Fin m => y s j)) i
      = Vec.sum (fun s : Fin m => Mat.apply M (y s) i) := by
  calc Mat.apply M (fun j => Vec.sum (fun s : Fin m => y s j)) i
      = Vec.sum (fun j : Fin n => Vec.sum (fun s : Fin m => CommRing.mul (M i j) (y s j))) :=
        Vec.sum_congr (fun j => Vec.mul_sum (M i j) (fun s : Fin m => y s j))
    _ = Vec.sum (fun s : Fin m => Vec.sum (fun j : Fin n => CommRing.mul (M i j) (y s j))) :=
        Vec.sum_exchange (fun (j : Fin n) (s : Fin m) => CommRing.mul (M i j) (y s j))

public theorem apply_qsmul {n : Nat} (M : Mat n n Rat) (c : Rat) (y : Vec n Rat) (i : Fin n) :
    Mat.apply M (fun j => c * y j) i = c * Mat.apply M y i := by
  calc Mat.apply M (fun j => c * y j) i
      = Vec.sum (fun j : Fin n => CommRing.mul c (CommRing.mul (M i j) (y j))) :=
        Vec.sum_congr (fun j => by
          show M i j * (c * y j) = c * (M i j * y j)
          rw [← Rat.mul_assoc, Rat.mul_comm (M i j) c, Rat.mul_assoc])
    _ = c * Mat.apply M y i := (Vec.mul_sum c (fun j : Fin n => CommRing.mul (M i j) (y j))).symm


namespace SpecSys

variable {nE n : Nat} (S : SpecSys nE n)

/-- The mirror of `e_eig`: the projections commute with `A` over `Q`. -/
public theorem e_eigL (t : Fin nE) (i j : Fin n) :
    Mat.mul (S.e t) S.Aq i j = ((S.lam t : Int) : Rat) * S.e t i j := by
  have hterm : ∀ k : Fin n, CommRing.mul (S.e t i k) (S.Aq k j)
      = (((fun k : Fin n => S.E t i k * S.A k j) k : Int) : Rat) * S.q⁻¹ := by
    intro k
    have hc : ((S.E t i k * S.A k j : Int) : Rat)
        = ((S.E t i k : Int) : Rat) * ((S.A k j : Int) : Rat) := Rat.intCast_mul _ _
    show (((S.E t i k : Int) : Rat) * S.q⁻¹) * ((S.A k j : Int) : Rat) = _
    rw [hc, Rat.mul_assoc, Rat.mul_comm S.q⁻¹ (((S.A k j : Int) : Rat)), ← Rat.mul_assoc]
  have hstep : Mat.mul (S.e t) S.Aq i j
      = ((Vec.sum (fun k : Fin n => S.E t i k * S.A k j) : Int) : Rat) * S.q⁻¹ := by
    calc Mat.mul (S.e t) S.Aq i j
        = Vec.sum (fun k : Fin n => CommRing.mul (S.e t i k) (S.Aq k j)) := rfl
      _ = Vec.sum (fun k : Fin n =>
            (((fun k : Fin n => S.E t i k * S.A k j) k : Int) : Rat) * S.q⁻¹) :=
          Vec.sum_congr hterm
      _ = _ := qsum_cast' (fun k : Fin n => S.E t i k * S.A k j) S.q⁻¹
  have heig : Vec.sum (fun k : Fin n => S.E t i k * S.A k j) = S.lam t * S.E t i j := S.eigL t i j
  rw [hstep, heig, Rat.intCast_mul]
  show (((S.lam t : Int) : Rat) * ((S.E t i j : Int) : Rat)) * S.q⁻¹ = _
  rw [Rat.mul_assoc]
  rfl

/-- `A` commutes with each projection. -/
public theorem e_comm (t : Fin nE) : Mat.mul (S.e t) S.Aq = Mat.mul S.Aq (S.e t) :=
  funext fun i => funext fun j => by rw [S.e_eigL t i j, S.e_eig t i j]

/-- Every vector is the sum of its five components. -/
public theorem apply_sum_e (x : Vec n Rat) (i : Fin n) :
    Vec.sum (fun t : Fin nE => Mat.apply (S.e t) x i) = x i := by
  calc Vec.sum (fun t : Fin nE => Mat.apply (S.e t) x i)
      = Vec.sum (fun j : Fin n => Vec.sum (fun t : Fin nE => CommRing.mul (S.e t i j) (x j))) :=
        Vec.sum_exchange (fun (t : Fin nE) (j : Fin n) => CommRing.mul (S.e t i j) (x j))
    _ = Vec.sum (fun j : Fin n =>
          CommRing.mul (Vec.sum (fun t : Fin nE => S.e t i j)) (x j)) :=
        Vec.sum_congr (fun j => (Vec.sum_mul (fun t : Fin nE => S.e t i j) (x j)).symm)
    _ = Vec.sum (fun j : Fin n => CommRing.mul ((Mat.id : Mat n n Rat) i j) (x j)) :=
        Vec.sum_congr (fun j => by rw [S.e_sum i j])
    _ = x i := congrFun (Mat.apply_id x) i

/-- Each component is an eigenvector. -/
public theorem apply_e_eig (t : Fin nE) (x : Vec n Rat) (i : Fin n) :
    Mat.apply S.Aq (Mat.apply (S.e t) x) i
      = ((S.lam t : Int) : Rat) * Mat.apply (S.e t) x i := by
  have h1 : Mat.apply S.Aq (Mat.apply (S.e t) x) = Mat.apply (Mat.mul S.Aq (S.e t)) x :=
    (Mat.apply_mul S.Aq (S.e t) x).symm
  rw [congrFun h1 i]
  have hterm : ∀ j : Fin n, CommRing.mul (Mat.mul S.Aq (S.e t) i j) (x j)
      = CommRing.mul (((S.lam t : Int) : Rat)) (CommRing.mul (S.e t i j) (x j)) := by
    intro j
    rw [S.e_eig t i j]
    exact CommRing.mul_assoc _ _ _
  show Vec.sum (fun j => CommRing.mul (Mat.mul S.Aq (S.e t) i j) (x j)) = _
  rw [Vec.sum_congr hterm, ← Vec.mul_sum]
  rfl

/-- A projection kills every eigenvector of a different eigenvalue. -/
public theorem apply_e_of_eig {s t : Fin nE} (hst : s ≠ t) (y : Vec n Rat)
    (hy : ∀ i, Mat.apply S.Aq y i = ((S.lam t : Int) : Rat) * y i) (i : Fin n) :
    Mat.apply (S.e s) y i = 0 := by
  have hcomm : Mat.apply (S.e s) (Mat.apply S.Aq y) i = Mat.apply S.Aq (Mat.apply (S.e s) y) i := by
    rw [← congrFun (Mat.apply_mul (S.e s) S.Aq y) i, S.e_comm s,
      congrFun (Mat.apply_mul S.Aq (S.e s) y) i]
  have hleft : Mat.apply (S.e s) (Mat.apply S.Aq y) i
      = ((S.lam t : Int) : Rat) * Mat.apply (S.e s) y i := by
    have hfun : Mat.apply S.Aq y = fun j => ((S.lam t : Int) : Rat) * y j := funext hy
    rw [hfun, apply_qsmul (S.e s) (((S.lam t : Int) : Rat)) y i]
  have hright : Mat.apply S.Aq (Mat.apply (S.e s) y) i
      = ((S.lam s : Int) : Rat) * Mat.apply (S.e s) y i := S.apply_e_eig s y i
  have hlam : ((S.lam t : Int) : Rat) ≠ ((S.lam s : Int) : Rat) := fun h =>
    S.lam_inj s t hst (Rat.intCast_inj.mp h).symm
  have hne : ((S.lam t : Int) : Rat) - ((S.lam s : Int) : Rat) ≠ 0 := by grind
  have heq : ((S.lam t : Int) : Rat) * Mat.apply (S.e s) y i
      = ((S.lam s : Int) : Rat) * Mat.apply (S.e s) y i := by
    rw [← hleft, ← hright, hcomm]
  have hz : (((S.lam t : Int) : Rat) - ((S.lam s : Int) : Rat)) * Mat.apply (S.e s) y i = 0 := by
    grind
  rcases Rat.mul_eq_zero.mp hz with h | h
  · exact absurd h hne
  · exact h

end SpecSys



/-! ### The algebra the projections span -/

namespace SpecSys

variable {nE n : Nat} (S : SpecSys nE n)

/-- Every power of `A` is the eigenvalue-weighted sum of the projections, so
the algebra generated by `A` sits inside their span. -/
public theorem e_pow (p : Nat) (i j : Fin n) :
    Vec.sum (fun t : Fin nE => ((S.lam t ^ p : Int) : Rat) * S.e t i j)
      = ((matPow S.A p i j : Int) : Rat) := by
  have hterm : ∀ t : Fin nE, ((S.lam t ^ p : Int) : Rat) * S.e t i j
      = (((fun t : Fin nE => S.lam t ^ p * S.E t i j) t : Int) : Rat) * S.q⁻¹ := by
    intro t
    have hc : ((S.lam t ^ p * S.E t i j : Int) : Rat)
        = ((S.lam t ^ p : Int) : Rat) * ((S.E t i j : Int) : Rat) := Rat.intCast_mul _ _
    show ((S.lam t ^ p : Int) : Rat) * (((S.E t i j : Int) : Rat) * S.q⁻¹) = _
    rw [hc, Rat.mul_assoc]
  have hint : Vec.sum (fun t : Fin nE => S.lam t ^ p * S.E t i j) = matPow S.A p i j * S.sc := by
    rw [Vec.sum_congr (fun t : Fin nE => (S.pow_eig t p i j).symm)]
    exact S.mul_sumE (matPow S.A p) i j
  rw [Vec.sum_congr hterm, qsum_cast' (fun t : Fin nE => S.lam t ^ p * S.E t i j) S.q⁻¹, hint,
    Rat.intCast_mul]
  show ((matPow S.A p i j : Int) : Rat) * S.q * S.q⁻¹ = _
  rw [Rat.mul_assoc, S.q_inv_cancel, Rat.mul_one]

/-- `e_t C e_t = Q e_t`: the corner the `t`-th projection cuts out of the
algebra spanned by the projections is one-dimensional. -/
public theorem e_sandwich (t : Fin nE) (c : Vec nE Rat) (i j : Fin n) :
    Mat.mul (Mat.mul (S.e t) (fun a b => Vec.sum (fun u : Fin nE => c u * S.e u a b)))
        (S.e t) i j = c t * S.e t i j := by
  have hmid : ∀ a b : Fin n,
      Mat.mul (S.e t) (fun a b => Vec.sum (fun u : Fin nE => c u * S.e u a b)) a b
        = c t * S.e t a b := by
    intro a b
    have hstep : ∀ k : Fin n,
        CommRing.mul (S.e t a k) (Vec.sum (fun u : Fin nE => c u * S.e u k b))
          = Vec.sum (fun u : Fin nE => CommRing.mul (c u) (CommRing.mul (S.e t a k) (S.e u k b))) := by
      intro k
      rw [Vec.mul_sum (S.e t a k) (fun u : Fin nE => c u * S.e u k b)]
      exact Vec.sum_congr (fun u => by
        show S.e t a k * (c u * S.e u k b) = c u * (S.e t a k * S.e u k b)
        rw [← Rat.mul_assoc, Rat.mul_comm (S.e t a k) (c u), Rat.mul_assoc])
    calc Mat.mul (S.e t) (fun a b => Vec.sum (fun u : Fin nE => c u * S.e u a b)) a b
        = Vec.sum (fun k : Fin n =>
            Vec.sum (fun u : Fin nE => CommRing.mul (c u) (CommRing.mul (S.e t a k) (S.e u k b)))) :=
          Vec.sum_congr hstep
      _ = Vec.sum (fun u : Fin nE =>
            Vec.sum (fun k : Fin n => CommRing.mul (c u) (CommRing.mul (S.e t a k) (S.e u k b)))) :=
          Vec.sum_exchange (fun (k : Fin n) (u : Fin nE) =>
            CommRing.mul (c u) (CommRing.mul (S.e t a k) (S.e u k b)))
      _ = Vec.sum (fun u : Fin nE => CommRing.mul (c u) (Mat.mul (S.e t) (S.e u) a b)) :=
          Vec.sum_congr (fun u => (Vec.mul_sum (c u)
            (fun k : Fin n => CommRing.mul (S.e t a k) (S.e u k b))).symm)
      _ = Vec.sum (fun u : Fin nE =>
            if t = u then CommRing.mul (c t) (S.e t a b) else AddCommGroup.zero) :=
          Vec.sum_congr (fun u => by
            by_cases hu : t = u
            · rw [if_pos hu]
              subst hu
              rw [S.e_idem t a b]
            · rw [if_neg hu, S.e_orth hu a b]
              exact Rat.mul_zero (c u))
      _ = c t * S.e t a b := Vec.sum_ite_eq t (fun _ => CommRing.mul (c t) (S.e t a b))
  have hfun : Mat.mul (S.e t) (fun a b => Vec.sum (fun u : Fin nE => c u * S.e u a b))
      = fun a b => c t * S.e t a b := funext fun a => funext fun b => hmid a b
  rw [hfun]
  have hlast : ∀ k : Fin n, CommRing.mul (c t * S.e t i k) (S.e t k j)
      = CommRing.mul (c t) (CommRing.mul (S.e t i k) (S.e t k j)) := by
    intro k
    show (c t * S.e t i k) * S.e t k j = c t * (S.e t i k * S.e t k j)
    rw [Rat.mul_assoc]
  show Vec.sum (fun k : Fin n => CommRing.mul (c t * S.e t i k) (S.e t k j)) = _
  rw [Vec.sum_congr hlast, ← Vec.mul_sum]
  show c t * Mat.mul (S.e t) (S.e t) i j = _
  rw [S.e_idem t i j]

/-- The general element of the algebra `C` the projections span. -/
@[expose] public def comb (c : Vec nE Rat) : Mat n n Rat :=
  fun a b => Vec.sum (fun u : Fin nE => CommRing.mul (c u) (S.e u a b))

/-- An idempotent of `C` that lies inside the component `e_t` is `0` or `e_t`:
the component has no proper invariant summand. This is the irreducibility half
of `RC1`, and it is read off `e_sandwich` -- the exact fact
`dim(e_t C e_t) = 1` of `S41c` -- rather than off a semisimplicity theorem. -/
public theorem e_minimal (t : Fin nE) (c : Vec nE Rat)
    (hne : ∃ p q : Fin n, S.e t p q ≠ 0)
    (hidem : ∀ i j : Fin n, Mat.mul (S.comb c) (S.comb c) i j = S.comb c i j)
    (hL : ∀ i j : Fin n, Mat.mul (S.e t) (S.comb c) i j = S.comb c i j)
    (hR : ∀ i j : Fin n, Mat.mul (S.comb c) (S.e t) i j = S.comb c i j) :
    (∀ i j : Fin n, S.comb c i j = 0) ∨ (∀ i j : Fin n, S.comb c i j = S.e t i j) := by
  have hRfun : Mat.mul (S.comb c) (S.e t) = S.comb c := funext fun a => funext fun b => hR a b
  have hsand : ∀ i j : Fin n, Mat.mul (Mat.mul (S.e t) (S.comb c)) (S.e t) i j
      = CommRing.mul (c t) (S.e t i j) := fun i j => S.e_sandwich t c i j
  have hkey : ∀ i j : Fin n, S.comb c i j = CommRing.mul (c t) (S.e t i j) := by
    intro i j
    have h1 : Mat.mul (Mat.mul (S.e t) (S.comb c)) (S.e t) i j
        = Mat.mul (S.e t) (Mat.mul (S.comb c) (S.e t)) i j :=
      Mat.mul_assoc_apply (S.e t) (S.comb c) (S.e t) i j
    rw [hsand i j, hRfun, hL i j] at h1
    exact h1.symm
  have hsq : ∀ i j : Fin n, Mat.mul (S.comb c) (S.comb c) i j
      = CommRing.mul (CommRing.mul (c t) (c t)) (S.e t i j) := by
    intro i j
    have hstep : ∀ k : Fin n, CommRing.mul (S.comb c i k) (S.comb c k j)
        = CommRing.mul (CommRing.mul (c t) (c t)) (CommRing.mul (S.e t i k) (S.e t k j)) := by
      intro k
      rw [hkey i k, hkey k j]
      show c t * S.e t i k * (c t * S.e t k j) = c t * c t * (S.e t i k * S.e t k j)
      rw [Rat.mul_assoc, Rat.mul_assoc, ← Rat.mul_assoc (S.e t i k) (c t) (S.e t k j),
        Rat.mul_comm (S.e t i k) (c t), Rat.mul_assoc]
    show Vec.sum (fun k : Fin n => CommRing.mul (S.comb c i k) (S.comb c k j)) = _
    rw [Vec.sum_congr hstep, ← Vec.mul_sum]
    exact congrArg (fun z => CommRing.mul (CommRing.mul (c t) (c t)) z) (S.e_idem t i j)
  obtain ⟨p, q, hpq⟩ := hne
  have hepq : S.e t p q * (S.e t p q)⁻¹ = 1 := Rat.mul_inv_cancel _ hpq
  have hc : c t * c t = c t := by
    have h1 : c t * c t * S.e t p q = c t * S.e t p q := by
      have h0 := hsq p q
      rw [hidem p q, hkey p q] at h0
      exact h0.symm
    have h2 := congrArg (fun z : Rat => z * (S.e t p q)⁻¹) h1
    show c t * c t = c t
    have h3 : c t * c t * (S.e t p q * (S.e t p q)⁻¹) = c t * (S.e t p q * (S.e t p q)⁻¹) := by
      rw [← Rat.mul_assoc, ← Rat.mul_assoc]
      exact h2
    rw [hepq, Rat.mul_one, Rat.mul_one] at h3
    exact h3
  by_cases h0 : c t = 0
  · refine Or.inl (fun i j => ?_)
    rw [hkey i j]
    show c t * S.e t i j = 0
    rw [h0]
    exact Rat.zero_mul _
  · have hc1 : c t = 1 := by
      have h2 := congrArg (fun z : Rat => z * (c t)⁻¹) hc
      have h3 : c t * (c t * (c t)⁻¹) = c t * (c t)⁻¹ := by
        rw [← Rat.mul_assoc]
        exact h2
      rw [Rat.mul_inv_cancel (c t) h0, Rat.mul_one] at h3
      exact h3
    refine Or.inr (fun i j => ?_)
    rw [hkey i j]
    show c t * S.e t i j = S.e t i j
    rw [hc1]
    exact Rat.one_mul _

end SpecSys


/-- `RC1`. The last of the twelve ambient lemmas of section 19.6, discharged
the way section 4.4 of the release plan fixes: through `S41a` and `S41c`, the
exact idempotent facts, rather than through a semisimplicity theorem.

The first three clauses are complete reducibility: the ambient rational space
is the direct sum of the eigenspaces of `A`, every vector splits as the sum of
its projections, each summand is an eigenvector, and any other such splitting
is that one. The last two are what the document's `RC1` is used for. The
fourth is `End(U_t) = Q`, the *real type* clause: every element of the algebra
`C` that the projections span is a scalar on the component `U_t = im(e_t)`,
which is `dim(e_t C e_t) = 1` of `S41c`. The fifth is *irreducibility* of
`U_t`: an idempotent of `C` lying inside `e_t` is `0` or `e_t`, so `U_t` has no
proper invariant summand.

Scope of the irreducibility clause. It is stated against invariant
**summands**, presented as idempotents of `C`, not against arbitrary invariant
subspaces. Passing from a subspace to a summand is exactly the semisimplicity
step that the release plan replaces by `S41a` and `S41c`; it is neither assumed
nor proved here. -/
public theorem RC1 {nE n : Nat} (S : SpecSys nE n) (x : Vec n Rat) :
    (∀ i, Vec.sum (fun t : Fin nE => Mat.apply (S.e t) x i) = x i)
      ∧ (∀ (t : Fin nE) (i : Fin n), Mat.apply S.Aq (Mat.apply (S.e t) x) i
          = ((S.lam t : Int) : Rat) * Mat.apply (S.e t) x i)
      ∧ (∀ y : Fin nE → Vec n Rat,
          (∀ (t : Fin nE) (i : Fin n), Mat.apply S.Aq (y t) i = ((S.lam t : Int) : Rat) * y t i) →
          (∀ i, Vec.sum (fun t : Fin nE => y t i) = x i) →
          ∀ (t : Fin nE) (i : Fin n), y t i = Mat.apply (S.e t) x i)
      ∧ (∀ (t : Fin nE) (c : Vec nE Rat) (i j : Fin n),
          Mat.mul (Mat.mul (S.e t) (S.comb c)) (S.e t) i j = c t * S.e t i j)
      ∧ (∀ (t : Fin nE) (c : Vec nE Rat), (∃ p q : Fin n, S.e t p q ≠ 0) →
          (∀ i j : Fin n, Mat.mul (S.comb c) (S.comb c) i j = S.comb c i j) →
          (∀ i j : Fin n, Mat.mul (S.e t) (S.comb c) i j = S.comb c i j) →
          (∀ i j : Fin n, Mat.mul (S.comb c) (S.e t) i j = S.comb c i j) →
          (∀ i j : Fin n, S.comb c i j = 0) ∨ (∀ i j : Fin n, S.comb c i j = S.e t i j)) := by
  refine ⟨S.apply_sum_e x, fun t i => S.apply_e_eig t x i, fun y hy hsum t i => ?_,
    fun t c i j => S.e_sandwich t c i j, fun t c => S.e_minimal t c⟩
  have hkill : ∀ (s u : Fin nE), s ≠ u → ∀ i, Mat.apply (S.e s) (y u) i = 0 :=
    fun s u hsu i => S.apply_e_of_eig hsu (y u) (fun k => hy u k) i
  have hself : ∀ (u : Fin nE) (i : Fin n), Mat.apply (S.e u) (y u) i = y u i := by
    intro u i
    have h1 : Vec.sum (fun s : Fin nE => Mat.apply (S.e s) (y u) i) = y u i :=
      S.apply_sum_e (y u) i
    have h2 : ∀ s : Fin nE, Mat.apply (S.e s) (y u) i
        = if u = s then Mat.apply (S.e u) (y u) i else AddCommGroup.zero := by
      intro s
      by_cases hs : u = s
      · rw [if_pos hs, hs]
      · rw [if_neg hs]
        exact hkill s u (fun h => hs h.symm) i
    rw [Vec.sum_congr h2, Vec.sum_ite_eq u (fun _ => Mat.apply (S.e u) (y u) i)] at h1
    exact h1
  have hx : Mat.apply (S.e t) x i = Mat.apply (S.e t) (y t) i := by
    have hxfun : x = fun j => Vec.sum (fun s : Fin nE => y s j) := funext (fun j => (hsum j).symm)
    rw [hxfun, apply_sum (S.e t) y i]
    have h2 : ∀ s : Fin nE, Mat.apply (S.e t) (y s) i
        = if t = s then Mat.apply (S.e t) (y t) i else AddCommGroup.zero := by
      intro s
      by_cases hs : t = s
      · rw [if_pos hs, hs]
      · rw [if_neg hs]
        exact hkill t s hs i
    rw [Vec.sum_congr h2, Vec.sum_ite_eq t (fun _ => Mat.apply (S.e t) (y t) i)]
  rw [hx, hself t i]

/-! ## The labelled spectral facts of the AtlasInstance -/

/-- The five eigenprojections of the AtlasInstance graph. -/
@[expose] public def xProj (t : Fin 5) : Mat 48 48 Rat := xSpec.e t

/-- The trace of a scaled projection is `48` times its rank. -/
public theorem xTraceE (t : Fin 5) :
    Vec.sum (fun i : Fin 48 => xEm t i i) = 48 * ((atlMult t.val : Nat) : Int) :=
  xSpec.trace_E_of_rank t (atlMult t.val) (xHasRank t)

/-- `S41`. The spectral decomposition of the AtlasInstance graph: five
projections on which `A_X` acts by `20, 8, 4, 0, -4`, recombining to `A_X`. -/
public theorem S41 :
    (∀ (t : Fin 5) (i j : Fin 48),
        Mat.mul xSpec.Aq (xProj t) i j = ((xLam t : Int) : Rat) * xProj t i j)
      ∧ (∀ i j : Fin 48, Vec.sum (fun t : Fin 5 => ((xLam t : Int) : Rat) * xProj t i j)
          = ((AX i j : Nat) : Rat))
      ∧ (xLam 0 = 20 ∧ xLam 1 = 8 ∧ xLam 2 = 4 ∧ xLam 3 = 0 ∧ xLam 4 = -4) := by
  refine ⟨fun t i j => xSpec.e_eig t i j, fun i j => ?_, by decide⟩
  have h : Vec.sum (fun t : Fin 5 => ((xLam t : Int) : Rat) * xProj t i j)
      = ((atlMat i j : Int) : Rat) := xSpec.e_decomp i j
  rw [h]
  norm_cast
  exact atlMat_adj i j

/-- `S41a`. The exact idempotent facts: `e_t^2 = e_t`, `e_s e_t = 0` for
distinct eigenvalues, and `sum_t e_t = 1`. No approximation, no eigenvector
and no real number enters: each is an identity of rational matrices. -/
public theorem S41a :
    (∀ (t : Fin 5) (i j : Fin 48), Mat.mul (xProj t) (xProj t) i j = xProj t i j)
      ∧ (∀ s t : Fin 5, s ≠ t → ∀ i j : Fin 48, Mat.mul (xProj s) (xProj t) i j = 0)
      ∧ (∀ i j : Fin 48,
          Vec.sum (fun t : Fin 5 => xProj t i j) = (Mat.id : Mat 48 48 Rat) i j) :=
  ⟨fun t i j => xSpec.e_idem t i j, fun _ _ hst i j => xSpec.e_orth hst i j,
    fun i j => xSpec.e_sum i j⟩

/-- `S41c`. The ranks of the five projections are `1, 2, 9, 18, 18`, each
certified by a split factorization; every power of `A_X` lies in their span,
so that span is the algebra `C` generated by `A_X`; and `e_t C e_t` is the
line `Q e_t`. -/
public theorem S41c :
    (∀ t : Fin 5, HasMatRank (xProj t) (atlMult t.val))
      ∧ (atlMult 0 = 1 ∧ atlMult 1 = 2 ∧ atlMult 2 = 9 ∧ atlMult 3 = 18 ∧ atlMult 4 = 18)
      ∧ (∀ (p : Nat) (i j : Fin 48),
          Vec.sum (fun t : Fin 5 => ((xLam t ^ p : Int) : Rat) * xProj t i j)
            = ((matPow atlMat p i j : Int) : Rat))
      ∧ (∀ (t : Fin 5) (c : Vec 5 Rat) (i j : Fin 48),
          Mat.mul (Mat.mul (xProj t) (fun a b => Vec.sum (fun u : Fin 5 => c u * xProj u a b)))
              (xProj t) i j = c t * xProj t i j) :=
  ⟨xHasRank, by decide, fun p i j => xSpec.e_pow p i j,
    fun t c i j => xSpec.e_sandwich t c i j⟩

/-- `RC1` at the AtlasInstance graph. -/
public theorem xRC1 (x : Vec 48 Rat) :
    (∀ i, Vec.sum (fun t : Fin 5 => Mat.apply (xProj t) x i) = x i)
      ∧ (∀ (t : Fin 5) (i : Fin 48), Mat.apply xSpec.Aq (Mat.apply (xProj t) x) i
          = ((xLam t : Int) : Rat) * Mat.apply (xProj t) x i)
      ∧ (∀ y : Fin 5 → Vec 48 Rat,
          (∀ (t : Fin 5) (i : Fin 48),
            Mat.apply xSpec.Aq (y t) i = ((xLam t : Int) : Rat) * y t i) →
          (∀ i, Vec.sum (fun t : Fin 5 => y t i) = x i) →
          ∀ (t : Fin 5) (i : Fin 48), y t i = Mat.apply (xProj t) x i) :=
  ⟨(RC1 xSpec x).1, (RC1 xSpec x).2.1, (RC1 xSpec x).2.2.1⟩


/-! ## `S41d`: the same decomposition at the class graph

The class graph needs no new table. `comb_mul` closes the algebra
`Z.I + Z.A + Z.J`, and the three projections are combinations in it: `J/120`
for the eigenvalue `56`, `(40 I + 10 A - 5 J)/120` for `8`, and
`(80 I - 10 A + 4 J)/120` for `-4`. Their traces are the multiplicities `T9`
pins by the trace system. -/

/-- The three eigenvalues of the class graph. -/
@[expose] public def kLam : Fin 3 → Int
  | 0 => 56
  | 1 => 8
  | _ => -4

/-- The three eigenprojections of the class graph, scaled by `120`. -/
@[expose] public def kEm : Fin 3 → Mat 120 120 Int
  | 0 => comb 0 0 1
  | 1 => comb 40 10 (-5)
  | _ => comb 80 (-10) 4

public theorem kA_comb : Aint = comb 0 1 0 :=
  funext fun u => funext fun v => by
    show Aint u v = 0 * (if u = v then 1 else 0) + 1 * Aint u v + 0
    omega

public def kSpec : SpecSys 3 120 where
  A := Aint
  lam := kLam
  E := kEm
  sc := 120
  sc_ne := by decide
  symmA := by
    intro u v
    show ((A u v : Nat) : Int) = ((A v u : Nat) : Int)
    rw [A_comm]
  symmE := by
    intro t u v
    have hA : Aint u v = Aint v u := by
      show ((A u v : Nat) : Int) = ((A v u : Nat) : Int)
      rw [A_comm]
    have hd : (if u = v then (1 : Int) else 0) = (if v = u then (1 : Int) else 0) := by
      by_cases h : u = v
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    match t with
    | 0 => show 0 * _ + 0 * Aint u v + 1 = 0 * _ + 0 * Aint v u + 1; rw [hA, hd]
    | 1 => show 40 * (if u = v then (1:Int) else 0) + 10 * Aint u v + (-5)
             = 40 * (if v = u then (1:Int) else 0) + 10 * Aint v u + (-5)
           rw [hA, hd]
    | 2 => show 80 * (if u = v then (1:Int) else 0) + (-10) * Aint u v + 4
             = 80 * (if v = u then (1:Int) else 0) + (-10) * Aint v u + 4
           rw [hA, hd]
  sumE := by
    intro u v
    show kEm 0 u v + (kEm 1 u v + (kEm 2 u v + 0)) = _
    show 0 * (if u = v then (1:Int) else 0) + 0 * Aint u v + 1
        + ((40 * (if u = v then (1:Int) else 0) + 10 * Aint u v + (-5))
          + ((80 * (if u = v then (1:Int) else 0) + (-10) * Aint u v + 4) + 0))
      = if u = v then (120 : Int) else 0
    by_cases h : u = v
    · rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]; omega
  eig := by
    intro t u v
    rw [kA_comb]
    match t with
    | 0 =>
      rw [show kEm 0 = comb 0 0 1 from rfl, comb_mul 0 1 0 0 0 1 u v]
      show 0 * (if u = v then (1:Int) else 0) + 0 * Aint u v + 56
        = 56 * (0 * (if u = v then (1:Int) else 0) + 0 * Aint u v + 1)
      omega
    | 1 =>
      rw [show kEm 1 = comb 40 10 (-5) from rfl, comb_mul 0 1 0 40 10 (-5) u v]
      show 320 * (if u = v then (1:Int) else 0) + 80 * Aint u v + (-40)
        = 8 * (40 * (if u = v then (1:Int) else 0) + 10 * Aint u v + (-5))
      omega
    | 2 =>
      rw [show kEm 2 = comb 80 (-10) 4 from rfl, comb_mul 0 1 0 80 (-10) 4 u v]
      show (-320) * (if u = v then (1:Int) else 0) + 40 * Aint u v + (-16)
        = (-4) * (80 * (if u = v then (1:Int) else 0) + (-10) * Aint u v + 4)
      omega
  lam_inj := by decide

/-- The traces of the three scaled projections: `120` times the multiplicities
`1`, `35`, `84`. -/
public theorem kTrace (t : Fin 3) (a c : Int)
    (h : ∀ u : K, kEm t u u = a + c) :
    Vec.sum (fun u : K => kEm t u u) = 120 * (a + c) := by
  rw [Vec.sum_congr h, Vec.sum_const, nsmulInt]
  rfl

/-- `S41d`. The spectral decomposition at the class graph: three orthogonal
idempotents summing to the identity, on which `A` acts by `56`, `8` and `-4`,
with traces the multiplicities `1`, `35`, `84` that `T9` pins. -/
public theorem S41d :
    (∀ (t : Fin 3) (u v : K), Mat.mul (kSpec.e t) (kSpec.e t) u v = kSpec.e t u v)
      ∧ (∀ s t : Fin 3, s ≠ t → ∀ u v : K, Mat.mul (kSpec.e s) (kSpec.e t) u v = 0)
      ∧ (∀ u v : K, Vec.sum (fun t : Fin 3 => kSpec.e t u v)
          = (Mat.id : Mat 120 120 Rat) u v)
      ∧ (∀ (t : Fin 3) (u v : K),
          Mat.mul kSpec.Aq (kSpec.e t) u v = ((kLam t : Int) : Rat) * kSpec.e t u v)
      ∧ Vec.sum (fun u : K => kEm 0 u u) = 120 * 1
      ∧ Vec.sum (fun u : K => kEm 1 u u) = 120 * 35
      ∧ Vec.sum (fun u : K => kEm 2 u u) = 120 * 84 := by
  refine ⟨fun t u v => kSpec.e_idem t u v, fun _ _ hst u v => kSpec.e_orth hst u v,
    fun u v => kSpec.e_sum u v, fun t u v => kSpec.e_eig t u v, ?_, ?_, ?_⟩
  · exact kTrace 0 0 1 (fun u => by
      show 0 * (if u = u then (1:Int) else 0) + 0 * Aint u u + 1 = 0 + 1
      rw [Aint_diag u]; omega)
  · exact kTrace 1 40 (-5) (fun u => by
      show 40 * (if u = u then (1:Int) else 0) + 10 * Aint u u + (-5) = 40 + (-5)
      rw [Aint_diag u, if_pos rfl]; omega)
  · exact kTrace 2 80 4 (fun u => by
      show 80 * (if u = u then (1:Int) else 0) + (-10) * Aint u u + 4 = 80 + 4
      rw [Aint_diag u, if_pos rfl]; omega)


/-! ## `S14`, `S15`, `S27`: the `(-4)`-eigenspace and the codimensions -/

public theorem sumsq_zero {n : Nat} (f : Vec n Int) (h : ∀ i, 0 ≤ f i)
    (hz : Vec.sum f = 0) (j : Fin n) : f j = 0 := by
  have h1 : f j ≤ Vec.sumInt f := sumInt_term_le f h j
  rw [Vec.sumInt_eq_sum, hz] at h1
  have h2 := h j
  omega

/-- `S14`. The `(-4)`-eigenspace of `A_X` is exactly the kernel of
`ProjGram(X)`, and exactly the space of linear relations `sum_i c_i P_i = 0`
among the projections of `X`. Rank-nullity applied to `c |-> sum_i c_i P_i`,
whose image is `span{P_i}` and whose kernel this is, is then the identity
`mult_{A_X}(-4) = |X| - rank(ProjGram(X))`: `rank(ProjGram(X))` is that
dimension because `ProjGram` is the Gram matrix of the `P_i` by `S13`. -/
public theorem S14 {m : Nat} (x : Fin m → K) (hinj : ∀ i j : Fin m, x i = x j → i = j)
    (c : Vec m Int) :
    ((∀ i : Fin m, Vec.sum (fun j : Fin m => ((A (x i) (x j) : Nat) : Int) * c j) = -4 * c i)
        ↔ (∀ i : Fin m, Vec.sum (fun j : Fin m => D55 x i j * c j) = 0))
      ∧ ((∀ i : Fin m, Vec.sum (fun j : Fin m => D55 x i j * c j) = 0)
        ↔ (∀ a b : Fin 8, gramComb x c a b = 0)) := by
  have hsplit : ∀ i : Fin m, Vec.sum (fun j : Fin m => D55 x i j * c j)
      = 4 * c i + Vec.sum (fun j : Fin m => ((A (x i) (x j) : Nat) : Int) * c j) := by
    intro i
    have hterm : ∀ j : Fin m, D55 x i j * c j
        = add (if i = j then 4 * c j else (AddCommGroup.zero : Int))
          (((A (x i) (x j) : Nat) : Int) * c j) := by
      intro j
      rw [D55_eq x hinj i j]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij]
        show (4 * 1 + ((A (x i) (x j) : Nat) : Int)) * c j
          = 4 * c j + ((A (x i) (x j) : Nat) : Int) * c j
        grind
      · rw [if_neg hij, if_neg hij]
        show (4 * 0 + ((A (x i) (x j) : Nat) : Int)) * c j
          = 0 + ((A (x i) (x j) : Nat) : Int) * c j
        grind
    rw [Vec.sum_congr hterm, Vec.sum_add (fun j : Fin m => if i = j then 4 * c j else zero)
      (fun j : Fin m => ((A (x i) (x j) : Nat) : Int) * c j),
      Vec.sum_ite_eq i (fun j : Fin m => 4 * c j)]
    rfl
  refine ⟨⟨fun h i => ?_, fun h i => ?_⟩, ⟨fun h => ?_, fun h i => ?_⟩⟩
  · rw [hsplit i, h i]; omega
  · have := hsplit i; rw [h i] at this; omega
  · have hzero : Vec.sum (fun i : Fin m =>
        Vec.sum (fun j : Fin m => c i * (c j * D55 x i j))) = 0 := by
      have hi : ∀ i : Fin m, Vec.sum (fun j : Fin m => c i * (c j * D55 x i j))
          = c i * Vec.sum (fun j : Fin m => D55 x i j * c j) := by
        intro i
        have hj : ∀ j : Fin m, c i * (c j * D55 x i j)
            = mul (c i) (D55 x i j * c j) := by
          intro j
          show c i * (c j * D55 x i j) = c i * (D55 x i j * c j)
          rw [Int.mul_comm (c j) (D55 x i j)]
        rw [Vec.sum_congr hj, ← Vec.mul_sum]
        rfl
      have hz : ∀ i : Fin m, Vec.sum (fun j : Fin m => c i * (c j * D55 x i j))
          = (AddCommGroup.zero : Int) := by
        intro i; rw [hi i, h i]; exact Int.mul_zero _
      rw [Vec.sum_congr hz]
      exact Vec.sum_zero
    have htf : tform (gramComb x c) (gramComb x c) = 0 := by
      rw [← (S13 x c).2.1, hzero]
      exact Int.mul_zero 16
    intro a b
    have houter : Vec.sum (fun p : Fin 8 =>
        Vec.sum (fun q : Fin 8 => gramComb x c p q * gramComb x c p q)) = 0 := htf
    have hrow : Vec.sum (fun q : Fin 8 => gramComb x c a q * gramComb x c a q) = 0 := by
      refine sumsq_zero (fun p : Fin 8 =>
        Vec.sum (fun q : Fin 8 => gramComb x c p q * gramComb x c p q)) (fun p => ?_) houter a
      rw [← Vec.sumInt_eq_sum]
      exact sumInt_nonneg _ (fun q => mul_self_nonneg _)
    have hcell := sumsq_zero (fun q : Fin 8 => gramComb x c a q * gramComb x c a q)
      (fun q => mul_self_nonneg _) hrow b
    rcases Int.mul_eq_zero.mp hcell with h' | h' <;> exact h'
  · have hz : tform (outer (rep (x i))) (gramComb x c) = 0 := by
      have hq : ∀ p q : Fin 8, mul (outer (rep (x i)) p q) (gramComb x c p q)
          = (AddCommGroup.zero : Int) := by
        intro p q; rw [h p q]; exact Int.mul_zero _
      show Vec.sum (fun p : Fin 8 => Vec.sum (fun q : Fin 8 =>
        mul (outer (rep (x i)) p q) (gramComb x c p q))) = 0
      rw [Vec.sum_congr (fun p => Vec.sum_congr (fun q => hq p q)),
        Vec.sum_congr (fun p : Fin 8 => Vec.sum_zero (n := 8) (α := Int))]
      exact Vec.sum_zero
    rw [tform_outer_left x c i] at hz
    have hterm : ∀ j : Fin m,
        c j * (dot (rep (x i)) (rep (x j)) * dot (rep (x i)) (rep (x j)))
          = mul 16 (D55 x i j * c j) := by
      intro j
      rw [← D55_exact x i j]
      show c j * (16 * D55 x i j) = 16 * (D55 x i j * c j)
      rw [Int.mul_comm (D55 x i j) (c j), ← Int.mul_assoc, Int.mul_comm (c j) 16, Int.mul_assoc]
    rw [Vec.sum_congr hterm, ← Vec.mul_sum] at hz
    have h16 : (16 : Int) * Vec.sum (fun j : Fin m => D55 x i j * c j) = 0 := hz
    omega

/-- `S15`. The codimension of `span{P_i : i in X}` inside `Sym^2(span X)`
along the tower -- ambient, residue, AtlasInstance, BlockFrame, block -- is
`0, 2, 6, 16, 0`. The dimension of `span{P_i}` is `|X| - mult_{A_X}(-4)` by
`S14` and rank-nullity, and `Sym^2` of a space of rank `r` has dimension
`r(r+1)/2`, which is `36` at rank `8` and `10` at rank `4`. -/
public theorem S15 :
    (ambLam 2 = -4 ∧ ambMult 2 = 84 ∧ 120 - 84 = 36 ∧ 36 - 36 = 0)
      ∧ (resLam 4 = -4 ∧ resMult 4 = 38 ∧ 72 - 38 = 34 ∧ 36 - 34 = 2)
      ∧ (atlLam 4 = -4 ∧ atlMult 4 = 18 ∧ 48 - 18 = 30 ∧ 36 - 30 = 6)
      ∧ (frmLam 2 = -4 ∧ frmMult 2 = 4 ∧ 24 - 4 = 20 ∧ 36 - 20 = 16)
      ∧ (blkLam 2 = -4 ∧ blkMult 2 = 2 ∧ 12 - 2 = 10 ∧ 10 - 10 = 0)
      ∧ (8 * (8 + 1) / 2 = 36 ∧ 4 * (4 + 1) / 2 = 10) := by decide

/-- `S27`. "codimension equals OrthFramePartition size" is refuted as a
pattern. It holds at the AtlasInstance -- codimension `6`, partition size `6`
by `S7` -- and fails at the residue, whose codimension is `2` while the
OrthFramePartition exhibited in `S11` has `9` parts. -/
public theorem S27 :
    (36 - (48 - atlMult 4) = 6 ∧ Nonempty (D54a atlSet 6 8))
      ∧ (36 - (72 - resMult 4) = 2 ∧ Nonempty (D54a (residue atlSet) 9 8)
          ∧ (2 : Nat) ≠ 9) :=
  ⟨⟨by decide, S7⟩, ⟨by decide, ⟨partition_of_partOK resFrameComp⟩, by decide⟩⟩

/-! ## `S23`, `S24`: the block and BlockFrame censuses as single orbits

This module imports no group layer, so the acting group is a **parameter**.
What is proved is the orbit statement itself: under preservation and
reachability the census is exactly the orbit of the exhibited representative,
with `blkSet 0` and `frame0` as those representatives. The counts
`|Blk| = 3150` and `|Frm| = 1575` are enumerations this module does not carry
out and are not asserted here. -/

/-- `S23`. The blocks form a single orbit, with the exhibited block as
representative. -/
public theorem S23 {G : Type} (act : G → Bitset → Bitset)
    (hpres : ∀ (g : G) (B : Bitset), Blk B → Blk (act g B))
    (hreach : ∀ B : Bitset, Blk B → ∃ g : G, act g (blkSet 0) = B) :
    Blk (blkSet 0) ∧ ∀ B : Bitset, Blk B ↔ ∃ g : G, act g (blkSet 0) = B := by
  refine ⟨blkIsBlock 0, fun B => ⟨hreach B, ?_⟩⟩
  rintro ⟨g, hg⟩
  exact hg ▸ hpres g (blkSet 0) (blkIsBlock 0)

/-- `S24`. The BlockFrames form a single orbit, with the exhibited BlockFrame
`{B_0, B_3}` as representative. -/
public theorem S24 {G : Type} (act : G → Bitset → Bitset)
    (hpres : ∀ (g : G) (B B' : Bitset), Frm B B' → Frm (act g B) (act g B'))
    (hreach : ∀ B B' : Bitset, Frm B B' →
      ∃ g : G, act g (blkSet 0) = B ∧ act g (blkSet 3) = B') :
    Frm (blkSet 0) (blkSet 3)
      ∧ ∀ B B' : Bitset, Frm B B'
          ↔ ∃ g : G, act g (blkSet 0) = B ∧ act g (blkSet 3) = B' := by
  refine ⟨frm03, fun B B' => ⟨hreach B B', ?_⟩⟩
  rintro ⟨g, hg, hg'⟩
  rw [← hg, ← hg']
  exact hpres g (blkSet 0) (blkSet 3) frm03

/-! ## `S19`: the three tower properties fail off the tower

Four class sets that are not scales of the tower, each a clique of the class
graph together with one class orthogonal to all of it. Each fails all three
tower properties: it is not regular, its frame operator is not a multiple of an
idempotent -- so it is not a `2`-design on its span, `D57` -- and it carries an
exhibited integer eigenvector whose eigenvalue is outside `{8,4,0,-4}` and is
not divisible by `4`, refuting `S18` and `S20` off the tower. -/

@[expose] public def offTab : Fin 4 → Nat := fun t =>
  if t.val = 0 then 2359808 else if t.val = 1 then 738460160
  else if t.val = 2 then 214849290752 else 33506551805510144

@[expose] public def offCard : Fin 4 → Nat := fun t =>
  if t.val = 0 then 3 else if t.val = 1 then 4 else if t.val = 2 then 5 else 7

@[expose] public def offEig : Fin 4 → Nat := fun t =>
  if t.val = 0 then 1 else if t.val = 1 then 2 else if t.val = 2 then 3 else 5

@[expose] public def offIdx (t : Fin 4) (i : Nat) : Nat := (offTab t >>> (8 * i)) &&& 255

@[expose] public def offSet (t : Fin 4) : Bitset :=
  unionUpto (fun i => Bitset.singleton (offIdx t i)) (offCard t)

@[expose] public def offVec (t : Fin 4) (i : Nat) : Nat := if i + 1 = offCard t then 0 else 1

@[expose] public def offClass (t : Fin 4) (i : Nat) : K :=
  ⟨offIdx t i % 120, Nat.mod_lt _ (by decide)⟩

/-- The two positions at which the frame operator's square fails to be
proportional to it. -/
@[expose] public def offPos : Fin 4 → Fin 8 := fun t => if t.val = 3 then 0 else 1

public theorem S19Comp :
    allFin (fun t : Fin 4 =>
      allLt (fun i => decide (offIdx t i < 120)) (offCard t)
      && allLt (fun i => decide (sumN (fun j => adjN (offIdx t i) (offIdx t j) * offVec t j)
            (offCard t) = offEig t * offVec t i)) (offCard t)
      && decide (degN (offSet t) (offIdx t 0) = offEig t)
      && decide (degN (offSet t) (offIdx t (offCard t - 1)) = 0)
      && decide (0 < offEig t)
      && decide (3 ≤ offCard t)) = true := by decide +kernel

public theorem S19Design :
    allFin (fun t : Fin 4 =>
      decide (Mat.mul (frameSum (offSet t)) (frameSum (offSet t)) 0 0
          * frameSum (offSet t) (offPos t) 1
        ≠ Mat.mul (frameSum (offSet t)) (frameSum (offSet t)) (offPos t) 1
          * frameSum (offSet t) 0 0)) = true := by decide +kernel

public theorem offIdx_lt (t : Fin 4) (i : Nat) (hi : i < offCard t) : offIdx t i < 120 :=
  of_decide_eq_true (allLt_true _ _
    (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp
      (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp
        (allFin_true _ S19Comp t)).1).1).1).1).1 i hi)

public theorem offClass_val (t : Fin 4) (i : Nat) (hi : i < offCard t) :
    (offClass t i).val = offIdx t i := Nat.mod_eq_of_lt (offIdx_lt t i hi)

public theorem offMem (t : Fin 4) (i : Nat) (hi : i < offCard t) :
    (offClass t i).val ∈ offSet t := by
  rw [offClass_val t i hi]
  exact (mem_unionUpto _ _ (offCard t)).mpr ⟨i, hi, (Bitset.mem_singleton _ _).mpr rfl⟩

/-- `S19`. -/
public theorem S19 (t : Fin 4) :
    (∃ u v : K, u.val ∈ offSet t ∧ v.val ∈ offSet t ∧ D14 (offSet t) u ≠ D14 (offSet t) v)
      ∧ (¬ ∃ c : Int, ∀ a b : Fin 8,
          Mat.mul (frameSum (offSet t)) (frameSum (offSet t)) a b
            = c * frameSum (offSet t) a b)
      ∧ (offVec t 0 ≠ 0
          ∧ (∀ i, i < offCard t →
              sumN (fun j => A (offClass t i) (offClass t j) * offVec t j) (offCard t)
                = offEig t * offVec t i)
          ∧ offEig t ≠ 8 ∧ offEig t ≠ 4 ∧ offEig t ≠ 0 ∧ offEig t % 4 ≠ 0) := by
  have hE : ∀ s : Fin 4, offEig s ≠ 8 ∧ offEig s ≠ 4 ∧ offEig s ≠ 0 ∧ offEig s % 4 ≠ 0 := by
    decide
  have hc := allFin_true _ S19Comp t
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  have hcard : 3 ≤ offCard t := of_decide_eq_true h6
  have hpos : 0 < offEig t := of_decide_eq_true h5
  refine ⟨⟨offClass t 0, offClass t (offCard t - 1), offMem t 0 (by omega),
      offMem t (offCard t - 1) (by omega), ?_⟩, ?_, ?_, fun i hi => ?_,
    (hE t).1, (hE t).2.1, (hE t).2.2.1, (hE t).2.2.2⟩
  · rw [D14_eq_degN, D14_eq_degN, offClass_val t 0 (by omega),
      offClass_val t (offCard t - 1) (by omega), of_decide_eq_true h3, of_decide_eq_true h4]
    omega
  · rintro ⟨q, hq⟩
    have hne := of_decide_eq_true (allFin_true _ S19Design t)
    rw [hq 0 0, hq (offPos t) 1] at hne
    exact hne (by grind)
  · show (if (0 : Nat) + 1 = offCard t then 0 else 1) ≠ 0
    rw [if_neg (by omega)]
    exact (by decide)
  · have he := of_decide_eq_true (allLt_true _ _ h2 i hi)
    rw [← he]
    refine sumN_congr_lt _ _ (offCard t) (fun j hj => ?_)
    show A (offClass t i) (offClass t j) * offVec t j = adjN (offIdx t i) (offIdx t j) * offVec t j
    show adjN (offClass t i).val (offClass t j).val * offVec t j = _
    rw [offClass_val t i hi, offClass_val t j hj]

/-! ## `S26`: Cauchy interlacing, exactly

`lambda_2(A_X) <= 8` for every induced subgraph is the Courant-Fischer
characterisation read on one explicit codimension-one subspace: the vectors of
`Q^X`, extended by zero, that are orthogonal to the all-ones vector of `K`. On
that subspace the Rayleigh quotient of `A` is at most `8`, and the proof is an
identity over `Z` rather than a limit: `12(8|c|^2 - c^T A c) = |(8I - A)c|^2`,
a sum of squares. Every induced subgraph is covered because a vector supported
on `X` is such a vector. -/

@[expose] public def Ac (c : Vec 120 Int) : Vec 120 Int :=
  fun i => Vec.sum (fun j : K => Aint i j * c j)

public theorem Aint_symm (u v : K) : Aint u v = Aint v u := by
  show ((A u v : Nat) : Int) = ((A v u : Nat) : Int)
  rw [A_comm]

public theorem Ac_Ac (c : Vec 120 Int) (hz : Vec.sum c = 0) (j : K) :
    Ac (Ac c) j = 4 * Ac c j + 32 * c j := by
  have hin : ∀ i : K, Aint j i * Ac c i
      = Vec.sum (fun k : K => mul (Aint j i) (Aint i k * c k)) := by
    intro i
    exact Vec.mul_sum (Aint j i) (fun k : K => Aint i k * c k)
  have hexch : Vec.sum (fun i : K => Vec.sum (fun k : K => mul (Aint j i) (Aint i k * c k)))
      = Vec.sum (fun k : K => Vec.sum (fun i : K => mul (Aint j i) (Aint i k * c k))) :=
    Vec.sum_exchange (fun (i : K) (k : K) => mul (Aint j i) (Aint i k * c k))
  have hgroup : ∀ k : K, Vec.sum (fun i : K => mul (Aint j i) (Aint i k * c k))
      = mul (Mat.mul Aint Aint j k) (c k) := by
    intro k
    have h1 : ∀ i : K, mul (Aint j i) (Aint i k * c k)
        = mul (mul (Aint j i) (Aint i k)) (c k) := by
      intro i
      show Aint j i * (Aint i k * c k) = Aint j i * Aint i k * (c k)
      rw [Int.mul_assoc]
    rw [Vec.sum_congr h1, ← Vec.sum_mul]
    rfl
  have hsq : ∀ k : K, Mat.mul Aint Aint j k
      = 24 + 4 * Aint j k + (if j = k then 32 else 0) := by
    intro k
    rw [AA_apply j k, common_eq j k]
    show ((24 + 4 * A j k + (if j = k then 32 else 0) : Nat) : Int) = _
    by_cases h : j = k
    · rw [if_pos h, if_pos h]
      show ((24 + 4 * A j k + 32 : Nat) : Int) = 24 + 4 * ((A j k : Nat) : Int) + 32
      omega
    · rw [if_neg h, if_neg h]
      show ((24 + 4 * A j k + 0 : Nat) : Int) = 24 + 4 * ((A j k : Nat) : Int) + 0
      omega
  have hfinal : ∀ k : K, mul (Mat.mul Aint Aint j k) (c k)
      = add (mul 24 (c k)) (add (mul 4 (Aint j k * c k))
          (if j = k then 32 * c k else zero)) := by
    intro k
    rw [hsq k]
    by_cases h : j = k
    · rw [if_pos h, if_pos h]
      show (24 + 4 * Aint j k + 32) * c k = 24 * c k + (4 * (Aint j k * c k) + 32 * c k)
      grind
    · rw [if_neg h, if_neg h]
      show (24 + 4 * Aint j k + 0) * c k = 24 * c k + (4 * (Aint j k * c k) + 0)
      grind
  show Vec.sum (fun i : K => Aint j i * Ac c i) = _
  rw [Vec.sum_congr hin, hexch, Vec.sum_congr hgroup, Vec.sum_congr hfinal,
    Vec.sum_add (fun k : K => mul 24 (c k))
      (fun k : K => add (mul 4 (Aint j k * c k)) (if j = k then 32 * c k else zero)),
    Vec.sum_add (fun k : K => mul 4 (Aint j k * c k))
      (fun k : K => if j = k then 32 * c k else zero),
    ← Vec.mul_sum 4 (fun k : K => Aint j k * c k),
    ← Vec.mul_sum 24 (fun k : K => c k),
    Vec.sum_ite_eq j (fun k : K => 32 * c k), hz]
  show (24 : Int) * 0 + (4 * Ac c j + 32 * c j) = 4 * Ac c j + 32 * c j
  omega

public theorem Ac_sq (c : Vec 120 Int) :
    Vec.sum (fun i : K => Ac c i * Ac c i)
      = Vec.sum (fun j : K => c j * Ac (Ac c) j) := by
  have hin : ∀ i : K, Ac c i * Ac c i
      = Vec.sum (fun j : K => mul (Ac c i) (Aint i j * c j)) := by
    intro i
    exact Vec.mul_sum (Ac c i) (fun j : K => Aint i j * c j)
  have hexch : Vec.sum (fun i : K => Vec.sum (fun j : K => mul (Ac c i) (Aint i j * c j)))
      = Vec.sum (fun j : K => Vec.sum (fun i : K => mul (Ac c i) (Aint i j * c j))) :=
    Vec.sum_exchange (fun (i : K) (j : K) => mul (Ac c i) (Aint i j * c j))
  have hcol : ∀ j : K, Vec.sum (fun i : K => mul (Ac c i) (Aint i j * c j))
      = c j * Ac (Ac c) j := by
    intro j
    have h1 : ∀ i : K, mul (Ac c i) (Aint i j * c j) = mul (c j) (Aint j i * Ac c i) := by
      intro i
      rw [Aint_symm j i]
      show Ac c i * (Aint i j * c j) = c j * (Aint i j * Ac c i)
      grind
    rw [Vec.sum_congr h1, ← Vec.mul_sum]
    rfl
  rw [Vec.sum_congr hin, hexch, Vec.sum_congr hcol]

/-- `S26`. -/
public theorem S26 (c : Vec 120 Int) (hz : Vec.sum c = 0) :
    Vec.sum (fun i : K => (8 * c i - Ac c i) * (8 * c i - Ac c i))
        + 12 * Vec.sum (fun i : K => c i * Ac c i)
      = 96 * Vec.sum (fun i : K => c i * c i)
    ∧ Vec.sum (fun i : K => c i * Ac c i) ≤ 8 * Vec.sum (fun i : K => c i * c i) := by
  have hsq : Vec.sum (fun i : K => Ac c i * Ac c i)
      = 4 * Vec.sum (fun i : K => c i * Ac c i)
        + 32 * Vec.sum (fun i : K => c i * c i) := by
    rw [Ac_sq c]
    have h1 : ∀ j : K, c j * Ac (Ac c) j
        = add (mul 4 (c j * Ac c j)) (mul 32 (c j * c j)) := by
      intro j
      rw [Ac_Ac c hz j]
      show c j * (4 * Ac c j + 32 * c j) = 4 * (c j * Ac c j) + 32 * (c j * c j)
      grind
    rw [Vec.sum_congr h1, Vec.sum_add (fun j : K => mul 4 (c j * Ac c j))
      (fun j : K => mul 32 (c j * c j)), ← Vec.mul_sum, ← Vec.mul_sum]
    rfl
  have hexp : Vec.sum (fun i : K => (8 * c i - Ac c i) * (8 * c i - Ac c i))
      = 64 * Vec.sum (fun i : K => c i * c i)
        + (neg (16 * Vec.sum (fun i : K => c i * Ac c i))
          + Vec.sum (fun i : K => Ac c i * Ac c i)) := by
    have h1 : ∀ i : K, (8 * c i - Ac c i) * (8 * c i - Ac c i)
        = add (mul 64 (c i * c i))
            (add (neg (mul 16 (c i * Ac c i))) (Ac c i * Ac c i)) := by
      intro i
      show (8 * c i - Ac c i) * (8 * c i - Ac c i)
        = 64 * (c i * c i) + (-(16 * (c i * Ac c i)) + Ac c i * Ac c i)
      grind
    rw [Vec.sum_congr h1, Vec.sum_add (fun i : K => mul 64 (c i * c i))
      (fun i : K => add (neg (mul 16 (c i * Ac c i))) (Ac c i * Ac c i)),
      Vec.sum_add (fun i : K => neg (mul 16 (c i * Ac c i)))
        (fun i : K => Ac c i * Ac c i),
      Vec.sum_neg (fun i : K => mul 16 (c i * Ac c i)),
      ← Vec.mul_sum, ← Vec.mul_sum]
    rfl
  have hnn : 0 ≤ Vec.sum (fun i : K => (8 * c i - Ac c i) * (8 * c i - Ac c i)) := by
    rw [← Vec.sumInt_eq_sum]
    exact sumInt_nonneg _ (fun i => mul_self_nonneg _)
  have hid : Vec.sum (fun i : K => (8 * c i - Ac c i) * (8 * c i - Ac c i))
      + 12 * Vec.sum (fun i : K => c i * Ac c i)
      = 96 * Vec.sum (fun i : K => c i * c i) := by
    rw [hexp, hsq]
    show 64 * Vec.sum (fun i : K => c i * c i)
      + (-(16 * Vec.sum (fun i : K => c i * Ac c i))
        + (4 * Vec.sum (fun i : K => c i * Ac c i)
          + 32 * Vec.sum (fun i : K => c i * c i)))
      + 12 * Vec.sum (fun i : K => c i * Ac c i) = _
    omega
  exact ⟨hid, by omega⟩




/-! ## `S9a`, `D58`, `S25`: how many OrthFrames there are

The count of OrthFrames is a clique enumeration in the orthogonality graph, run
here on the packed neighbourhood table `orthTable` and keyed on the least
vertex of each clique, which is exactly the shape section 17 gives it. -/

/-- The orthogonality neighbourhood of every class, packed `120` bits per row.
Nothing about the table is asserted: `orthRowComp` re-derives every row from
`orthNbr`, which is `dot`. -/
@[expose] public def orthTable : Nat := 2892042409135679521223517033186388416685411899845586750577805763355700015807315482243063236581858381628702598740982190805574565855910995135609529094806872195380938034505951791926614052171851233997262337542978615969256574336402243790845153346115424001087936940798916566209770341611915126725219846743755685656603734449641247403584367952585399387956078485456642680823324004386183006489052152826242127050509822578914588363261223851799967175084512049173005353042319170106805349594905575954949796362337525247463981145369225551674142184867052264018890037482611084904318126649268607731852052421302669475456193672506381034933953144431357677920839321014462773798180107935890136623460617231138017948934357290627200763551022386252854110275456911610913328871370213363031453531874696564088342735076772781809486930602133782534259259492794814776978027025379718198191605388834270832376504317195772322568820887002498670990029641368261492373127317773434720509527367125044810755985490929317920123378533022057060599263385008886291460016297912312881825453072225874423858228015999989316749192868769102295135955606750592997024037779877688592301581918786822223437433837324182536192473788395104162273768363463050053389695238825908239374677801222366119464824097975467121533790809520366522493681800940841620419673334956350255566150919729434037929190911429048187840704775015525469373373107335505101674293317178126107094325818652432838634141190972908379042157037151200899392348351666792155236831183532356021162730228448634403585487553415100241913088512203507941405986129522823141874721755312536663120807722132709168911995834914444873612522406043808405734136247605706667495469852638585134853346681619723579643600907410507718493234764225321539202002049771196140894010866881177010886462094045108863563737800836233028089959879435276087399757183448593190804958726786481807608745148975421206624346465085307847015853676171462663097635643931695044866735447290337626887584308660798113668046363522019170065813590785765298799971163294225034597082217854577678244084900622573215469491503733104553854672381329890907455390099036664319356705419926038709078593510987606433283731403458514396515252375592501864241004923672332184528812327344705876567205936317977262026179786586957238626075939393389161065326321340826679130737629868530955142277442526900350318009510901709613883618904392004682599474497068996026588645956462736295511261565385749971567231712589337626989731183270242594870081253186155226945116916375230257622112610159935869826518701551793859740793359429485072748097281288393664684937237368602458982493191685170744185815236143221434518167097176558490776859066589190348566180166978040711078449522149133952486080130949558909896908321217111206344024076708546185275513575728880617554437494908142455184809336805979315021064045511985030670578816507115911918517119702411774648725666745963252215978459401283687476130499620052894037725246553299253013217249162018066287532181522441855775388935048418753130157056177872904172784919596622333027496158244684152733513113674330862836660594528833169167429267049873933112340858641183572723627560788473286403837418692952610868509848127337041816186330158624765843989400953414384573434242728279609977258422823730200995134847092834374042021693351749340517550644013966100289977980598063724305128761313229417327206206084565383318031272227672985271011241964651407412345676805288248115527311273025957783602134659742201025720260008512663316587237573766683919544211527857966633997993799722564243794959047138905063271808503312626411402313045910592593172616707610569916161964073563818190741534746171045036315086211012091707684264467571838900981487619837974956824979263076172387368131681533283967568102698150147315976044424259391362659380481334857921697944130922275795898812947864615095442542729287800724693777309498718823756520771056385405572777381971729433250323286084021741920445783711787043465401422591132362380299345900916543121301261438228142083115197826141300382909306409862067672378244715932385563759900391130610194613208300204414359691454041974691014170574709720529000247387514565857469325291120949250153056125351510174480804058272852063639410615835562082710247469786498492441888047201769588822008562718764180772136580228284345014615443871217841042109721988940140468534164882880200452470632655842109326700638885569411601367505206758965141045250

@[expose] public def orthRow (i : Nat) : Nat := (orthTable >>> (120 * i)) &&& (2 ^ 120 - 1)

public theorem orthRowComp :
    allLt (fun i => decide (orthRow i = Bitset.toNat (orthNbr i 120))) 120 = true := by
  decide +kernel

/-- Walk the set bits of `c`, whose bit `t` names the class `off + t`, and sum
`f` over them. The fuel is the numeral itself, as in `Bitset.toList`. -/
@[expose] public def bitFold (f : Nat → Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih c off => if c = 0 then 0
      else (if c % 2 = 1 then f (c / 2) off else 0) + ih (c / 2) (off + 1)) fuel

/-- The number of `q`-cliques of the orthogonality graph inside the shifted
candidate set `c`, whose bit `t` names the class `off + t`. Each step fixes the
least remaining candidate and intersects with its neighbourhood above it, so
every clique is produced once, keyed on its least vertex. -/
@[expose] public def cliqCnt : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | q + 1, c, off =>
      bitFold (fun c' o => cliqCnt q (c' &&& (orthRow o >>> (o + 1))) (o + 1)) c c off

/-- The OrthFrames of `S` of size `q + 1` whose least class is `v`. -/
@[expose] public def framesFrom (S : Bitset) (q v : Nat) : Nat :=
  cliqCnt q ((Bitset.toNat S >>> (v + 1)) &&& (orthRow v >>> (v + 1))) (v + 1)

/-- All OrthFrames of `S` of size `q`, keyed on the least class of each. -/
@[expose] public def framesIn (S : Bitset) (q : Nat) : Nat :=
  sumN (fun v => if v ∈ S then framesFrom S (q - 1) v else 0) 120

/-- `D58`. `max_cliques_from_least`: the number of OrthFrames the enumeration
produces from the least class of `K`. -/
@[expose] public def D58 : Nat := framesFrom fullK 7 0

public theorem D58_val : D58 = 135 := by decide +kernel

/-- `S25`. The clique-enumeration cap `6000` is never approached: at most `135`
cliques come from the least vertex. The cap is therefore vacuous rather than an
assumption -- nothing in section 17 depends on it. -/
public theorem S25 : D58 = 135 ∧ D58 ≤ 6000 ∧ D58 * 44 < 6000 :=
  ⟨D58_val, by rw [D58_val]; decide, by rw [D58_val]; decide⟩

/-- An OrthFrame of `K` and of the AtlasInstance that is a part of neither
exhibited OrthFramePartition. -/
@[expose] public def extraFrame : Bitset := Bitset.ofNat 13721905315971075

public theorem D54_of {S F : Bitset} {n : Nat}
    (h : (Bitset.subset F S && decide (Bitset.card F = n) && pwOrthOK F) = true) :
    D54 S F n := by
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, of_decide_eq_true h.1.2, pwOrth_of h.2⟩

public theorem extraComp :
    ((Bitset.subset extraFrame fullK && decide (Bitset.card extraFrame = 8)
        && pwOrthOK extraFrame) = true)
      ∧ ((Bitset.subset extraFrame atlSet && decide (Bitset.card extraFrame = 8)
        && pwOrthOK extraFrame) = true)
      ∧ allLt (fun a => !decide (extraFrame = frameAt kFrameTable a)) 15 = true
      ∧ allLt (fun a => !decide (extraFrame = frameAt atlFrameTable a)) 6 = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

public theorem framesComp :
    framesIn (blkSet 0) 4 = 3 ∧ framesIn atlSet 8 = 36 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- `S9a`. The number of **all** OrthFrames is not the size of an
OrthFramePartition. Inside a block the two agree: the enumeration finds three
frames and the partition of `S1` has three parts. At the AtlasInstance the
enumeration finds `36` against the six parts of `S7`. At `K` the count is
larger still: `extraFrame` is an OrthFrame of `K` -- and of the AtlasInstance
-- that is none of the fifteen parts of `S8` nor of the six of `S7`, so the
`15` of `S8` is not the number of OrthFrames either. -/
public theorem S9a :
    (framesIn (blkSet 0) 4 = 3 ∧ Nonempty (D54a (blkSet 0) 3 4))
      ∧ (framesIn atlSet 8 = 36 ∧ Nonempty (D54a atlSet 6 8) ∧ (36 : Nat) ≠ 6)
      ∧ (D54 fullK extraFrame 8 ∧ ∀ a, a < 15 → extraFrame ≠ frameAt kFrameTable a)
      ∧ (D54 atlSet extraFrame 8 ∧ ∀ a, a < 6 → extraFrame ≠ frameAt atlFrameTable a)
      ∧ Nonempty (D54a fullK 15 8) := by
  refine ⟨⟨framesComp.1, ⟨blkPart 0⟩⟩, ⟨framesComp.2, S7, by decide⟩,
    ⟨D54_of extraComp.1, fun a ha => ?_⟩, ⟨D54_of extraComp.2.1, fun a ha => ?_⟩, S8⟩
  · have h := allLt_true _ _ extraComp.2.2.1 a ha
    rw [Bool.not_eq_true'] at h
    exact of_decide_eq_false h
  · have h := allLt_true _ _ extraComp.2.2.2 a ha
    rw [Bool.not_eq_true'] at h
    exact of_decide_eq_false h

/-! ## `D61`, `S39`, `S40`: the frame operator on `Sym^2`, and the
isometry representation it commutes with -/

public theorem qsumN_congr (f g : Nat → Rat) :
    ∀ m, (∀ k, k < m → f k = g k) → qsumN f m = qsumN g m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ p ih =>
    intro h
    rw [qsumN_succ, qsumN_succ, h p (Nat.lt_succ_self p),
      ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

public theorem qsumN_smul (r : Rat) (f : Nat → Rat) :
    ∀ m, r * qsumN f m = qsumN (fun k => r * f k) m := by
  intro m
  induction m with
  | zero => exact Rat.mul_zero r
  | succ p ih => rw [qsumN_succ, qsumN_succ, ← ih, Rat.mul_add]

public theorem rat_cancel16 {a b : Rat} (h : 16 * a = 16 * b) : a = b := by
  have h1 : (16 : Rat)⁻¹ * (16 * a) = (16 : Rat)⁻¹ * (16 * b) := by rw [h]
  rw [← Rat.mul_assoc, ← Rat.mul_assoc, Rat.inv_mul_cancel 16 (by decide),
    Rat.one_mul, Rat.one_mul] at h1
  exact h1

/-- `ProjGram` on classes rather than on a listing: `4 delta + A`. -/
@[expose] public def pgram (u v : K) : Int := 4 * (if u = v then 1 else 0) + ((A u v : Nat) : Int)

/-- The trace form on two projections, cleared of its denominator:
`4 tr(P_u P_v) = ProjGram[u][v]`. This is `S35` and `dot_rep_sq` in one. -/
public theorem four_trace_proj (u v : K) :
    4 * traceQ (Mat.mul (projQ u) (projQ v)) = ((pgram u v : Int) : Rat) := by
  have h := projQ_trace_dot u v
  rw [dot_rep_sq u v] at h
  have h16 : ((16 * (4 * (if u = v then 1 else 0) + ((A u v : Nat) : Int)) : Int) : Rat)
      = 16 * ((pgram u v : Int) : Rat) := by
    show ((16 * pgram u v : Int) : Rat) = _
    rw [Rat.intCast_mul 16 (pgram u v)]
    rfl
  rw [h16] at h
  refine rat_cancel16 ?_
  rw [← h]
  show (16 : Rat) * (4 * traceQ (Mat.mul (projQ u) (projQ v)))
    = 64 * traceQ (Mat.mul (projQ u) (projQ v))
  have h64 : (16 : Rat) * 4 = 64 := by decide +kernel
  rw [← Rat.mul_assoc, h64]

/-- `D61`. The frame operator of the class set `X`,
`S_X(Y) := sum_{i in X} tr(P_i Y) P_i`, an operator on the symmetric matrices
`Sym^2(Q^8)`, a space of dimension `36`. -/
@[expose] public def D61 (W : Bitset) (Y : Mat 8 8 Rat) : Mat 8 8 Rat :=
  fun a b => qsumN (fun u => if u ∈ W then
    traceQ (Mat.mul (projQ (kOf u)) Y) * projQ (kOf u) a b else 0) 120

/-- The frame operator is the Gram operator of `D55`: on the projection
`P_j` it returns `sum_i tr(P_i P_j) P_i`, whose coefficients are exactly the
entries of `ProjGram(X)` divided by `4`. So `4 S_X` carries `ProjGram = 4I + A_X`
in the spanning family `{P_i}`, which is what ties `S_X` to `A_X`. -/
public theorem frameOp_gram (W : Bitset) (j : K) (a b : Fin 8) :
    4 * D61 W (projQ j) a b
      = qsumN (fun u => if u ∈ W then ((pgram (kOf u) j : Int) : Rat) * projQ (kOf u) a b
          else 0) 120 := by
  show 4 * qsumN (fun u => if u ∈ W then
      traceQ (Mat.mul (projQ (kOf u)) (projQ j)) * projQ (kOf u) a b else 0) 120 = _
  rw [qsumN_smul]
  refine qsumN_congr _ _ 120 (fun k _ => ?_)
  by_cases h : k ∈ W
  · rw [if_pos h, if_pos h, ← four_trace_proj (kOf k) j]
    show 4 * (traceQ (Mat.mul (projQ (kOf k)) (projQ j)) * projQ (kOf k) a b)
      = 4 * traceQ (Mat.mul (projQ (kOf k)) (projQ j)) * projQ (kOf k) a b
    rw [Rat.mul_assoc]
  · rw [if_neg h, if_neg h, Rat.mul_zero]

/-- The frame operator sends the identity to the frame operator of
`D57`: `S_X(I) = sum_{i in X} P_i`. The `2`-design condition of `S17` is
therefore a statement about `S_X` at one point of `Sym^2`. -/
public theorem frameOp_id (W : Bitset) (a b : Fin 8) :
    D61 W (Mat.id : Mat 8 8 Rat) a b = projSum W a b := by
  show qsumN (fun u => if u ∈ W then
      traceQ (Mat.mul (projQ (kOf u)) Mat.id) * projQ (kOf u) a b else 0) 120 = _
  refine qsumN_congr _ _ 120 (fun k _ => ?_)
  by_cases h : k ∈ W
  · rw [if_pos h, if_pos h]
    have hid : Mat.mul (projQ (kOf k)) (Mat.id : Mat 8 8 Rat) = projQ (kOf k) := by
      funext p q
      exact Mat.mul_id_apply (projQ (kOf k)) p q
    rw [hid, (projQ_symm_trace (kOf k)).2, Rat.one_mul]
  · rw [if_neg h, if_neg h]

/-- The spectrum of `S_X` at the AtlasInstance. `frameOp_gram` factors
`4 S_X = W G W^*` with `G = ProjGram(X) = 4I + A_X`, so the nonzero eigenvalues
of `S_X` are `1 + lambda/4` for the eigenvalues `lambda != -4` of `A_X`, with
the same multiplicities; `S14` and `S15` give the remaining multiplicity of `0`
as the codimension `36 - (|X| - mult(-4))`. At the AtlasInstance that is
`6, 3, 2, 1` with multiplicities `1, 2, 9, 18` and `0` with multiplicity `6`,
and `1 + 2 + 9 + 18 + 6 = 36 = dim Sym^2(Q^8)`. -/
public theorem sq_nonneg_int (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have h' : (0 : Int) ≤ -x := by omega
    have h2 := Int.mul_nonneg h' h'
    rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at h2
    exact h2

public theorem sq_ge_of_abs_ge {c x : Int} (hc : 0 ≤ c) (h : c ≤ x ∨ x ≤ -c) :
    c * c ≤ x * x := by
  rcases h with h | h
  · exact Int.mul_le_mul h h hc (by omega)
  · have h3 : (-x) * (-x) = x * x := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    have h2 : c * c ≤ (-x) * (-x) := Int.mul_le_mul (by omega) (by omega) hc (by omega)
    rw [h3] at h2
    exact h2

/-- The `k = 1` and `k = 2` trace equations already have a single solution in
the box the `k = 2` equation confines an integer solution to. -/
public theorem traceBoxComp :
    allLt (fun a => allLt (fun b => allLt (fun c =>
      !(decide (2 * ((a : Int) - 6) + 9 * ((b : Int) - 2) + 18 * ((c : Int) - 2) = 42)
            && decide (2 * (((a : Int) - 6) * ((a : Int) - 6))
              + 9 * (((b : Int) - 2) * ((b : Int) - 2))
              + 18 * (((c : Int) - 2) * ((c : Int) - 2)) = 72))
        || (decide ((a : Int) - 6 = 3) && decide ((b : Int) - 2 = 2)
            && decide ((c : Int) - 2 = 1))) 5) 5) 13 = true := by decide +kernel

public theorem traceBox (a b c : Nat) (ha : a < 13) (hb : b < 5) (hc : c < 5)
    (h1 : 2 * ((a : Int) - 6) + 9 * ((b : Int) - 2) + 18 * ((c : Int) - 2) = 42)
    (h2 : 2 * (((a : Int) - 6) * ((a : Int) - 6))
      + 9 * (((b : Int) - 2) * ((b : Int) - 2))
      + 18 * (((c : Int) - 2) * ((c : Int) - 2)) = 72) :
    ((a : Int) - 6 = 3 ∧ (b : Int) - 2 = 2 ∧ (c : Int) - 2 = 1) := by
  have h := allLt_true _ _ (allLt_true _ _ (allLt_true _ _ traceBoxComp a ha) b hb) c hc
  rw [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true h1, decide_eq_true h2] at h
  rcases h with hbad | hgood
  · exact absurd hbad (by decide)
  · rw [Bool.and_eq_true, Bool.and_eq_true] at hgood
    exact ⟨of_decide_eq_true hgood.1.1, of_decide_eq_true hgood.1.2,
      of_decide_eq_true hgood.2⟩

/-- The five scalars of `S41d` at the AtlasInstance are `6, 3, 2, 1, 0`
against the component dimensions `1, 2, 9, 18, 6`: they reproduce the integer
traces `tr(S_X^k) = 48, 108, 360` for `k = 1, 2, 3`, and `(3, 2, 1)` is the
unique INTEGER solution of that system once `6` and `0` are fixed by `S17` and
`S15`.

An earlier prose rendering called this a unique real solution. That is false:
the same three equations are also satisfied by approximately
`(3.190960144833, 0.732382694450, 1.612590858904)`.  The completed formal
semantics is integer uniqueness, and the canonical statement generated from
the migrated declaration is authoritative for `S43`.

So it is proved over `Z`, and proved rather than checked at a point: the `k = 2`
equation forces `x*x <= 36`, `y*y <= 8` and `z*z <= 4`, hence `|x| <= 6`,
`|y| <= 2`, `|z| <= 2`, and `traceBox` settles the finite box that leaves. The
bound is what makes the finite check a proof instead of a sample. -/
public theorem S43 :
    (1 * 6 + 2 * 3 + 9 * 2 + 18 * 1 + 6 * 0 = (48 : Int)
      ∧ 1 * (6 * 6) + 2 * (3 * 3) + 9 * (2 * 2) + 18 * (1 * 1) + 6 * (0 * 0) = (108 : Int)
      ∧ 1 * (6 * 6 * 6) + 2 * (3 * 3 * 3) + 9 * (2 * 2 * 2) + 18 * (1 * 1 * 1)
          + 6 * (0 * 0 * 0) = (360 : Int))
      ∧ (48 : Int) / 8 = 6
      ∧ (∀ x y z : Int,
          1 * 6 + 2 * x + 9 * y + 18 * z + 6 * 0 = 48 →
          1 * (6 * 6) + 2 * (x * x) + 9 * (y * y) + 18 * (z * z) + 6 * (0 * 0) = 108 →
          1 * (6 * 6 * 6) + 2 * (x * x * x) + 9 * (y * y * y) + 18 * (z * z * z)
            + 6 * (0 * 0 * 0) = 360 →
          x = 3 ∧ y = 2 ∧ z = 1) := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, fun x y z h1 h2 _ => ?_⟩
  have hx0 : (0 : Int) ≤ x * x := sq_nonneg_int x
  have hy0 : (0 : Int) ≤ y * y := sq_nonneg_int y
  have hz0 : (0 : Int) ≤ z * z := sq_nonneg_int z
  have hbox : ∀ X Y Z : Int, 0 ≤ X → 0 ≤ Y → 0 ≤ Z →
      1 * (6 * 6) + 2 * X + 9 * Y + 18 * Z + 6 * (0 * 0) = 108 →
      X ≤ 36 ∧ Y ≤ 8 ∧ Z ≤ 4 := by
    intro X Y Z hX hY hZ h
    omega
  obtain ⟨hxb, hyb, hzb⟩ := hbox (x * x) (y * y) (z * z) hx0 hy0 hz0 h2
  have hxr : -6 ≤ x ∧ x ≤ 6 := by
    refine ⟨Decidable.byCases (p := -6 ≤ x) (fun h => h) (fun h => ?_),
      Decidable.byCases (p := x ≤ 6) (fun h => h) (fun h => ?_)⟩
    · have h49 : (7 : Int) * 7 ≤ x * x := sq_ge_of_abs_ge (by decide) (Or.inr (by omega))
      omega
    · have h49 : (7 : Int) * 7 ≤ x * x := sq_ge_of_abs_ge (by decide) (Or.inl (by omega))
      omega
  have hyr : -2 ≤ y ∧ y ≤ 2 := by
    refine ⟨Decidable.byCases (p := -2 ≤ y) (fun h => h) (fun h => ?_),
      Decidable.byCases (p := y ≤ 2) (fun h => h) (fun h => ?_)⟩
    · have h9 : (3 : Int) * 3 ≤ y * y := sq_ge_of_abs_ge (by decide) (Or.inr (by omega))
      omega
    · have h9 : (3 : Int) * 3 ≤ y * y := sq_ge_of_abs_ge (by decide) (Or.inl (by omega))
      omega
  have hzr : -2 ≤ z ∧ z ≤ 2 := by
    refine ⟨Decidable.byCases (p := -2 ≤ z) (fun h => h) (fun h => ?_),
      Decidable.byCases (p := z ≤ 2) (fun h => h) (fun h => ?_)⟩
    · have h9 : (3 : Int) * 3 ≤ z * z := sq_ge_of_abs_ge (by decide) (Or.inr (by omega))
      omega
    · have h9 : (3 : Int) * 3 ≤ z * z := sq_ge_of_abs_ge (by decide) (Or.inl (by omega))
      omega
  have ex : (((x + 6).toNat : Nat) : Int) - 6 = x := by omega
  have ey : (((y + 2).toNat : Nat) : Int) - 2 = y := by omega
  have ez : (((z + 2).toNat : Nat) : Int) - 2 = z := by omega
  have hkey := traceBox (x + 6).toNat (y + 2).toNat (z + 2).toNat (by omega) (by omega) (by omega)
    (by rw [ex, ey, ez]; omega) (by rw [ex, ey, ez]; omega)
  rw [ex, ey, ez] at hkey
  exact hkey


/-! ## `Sym^2` in coordinates: the `36` the operator of `D61` runs in

`Sym^2(Q^O)` is presented by its upper triangle: `symTab` lists the `36` pairs
`(a,b)` with `a <= b`, `symInvTab` inverts that listing on all `64` pairs, and
`symCoord`/`symMat` are the resulting mutually inverse maps between symmetric
`8 x 8` matrices and `Q^36`. Neither table is assumed: `symComp` re-derives
both directions of the inversion by evaluation. -/

/-- The `36` upper-triangular index pairs, one byte `8a + b` each. -/
@[expose] public def symTab : Nat :=
  122807116652991033110195367307633744713947196998676880161575516212649129082649766396160

/-- The inverse listing on all `64` pairs, one byte each. -/
@[expose] public def symInvTab : Nat :=
  1840080359664264445547562854410205228995865677950264323898888642244154823635854429796292740204299504229429601729672796931636987102599071756038072564842752

@[expose] public def symA (k : Nat) : Nat := byteAt symTab k / 8 % 8

@[expose] public def symB (k : Nat) : Nat := byteAt symTab k % 8

@[expose] public def symOf (a b : Nat) : Nat := byteAt symInvTab (8 * a + b) % 36

public theorem symA_lt (k : Nat) : symA k < 8 := Nat.mod_lt _ (by decide)

public theorem symB_lt (k : Nat) : symB k < 8 := Nat.mod_lt _ (by decide)

public theorem symOf_lt (a b : Nat) : symOf a b < 36 := Nat.mod_lt _ (by decide)

public theorem symComp :
    allLt (fun k => decide (symOf (symA k) (symB k) = k)) 36 = true
      ∧ allLt (fun a => allLt (fun b =>
          decide (symA (symOf a b) = if a ≤ b then a else b)
            && decide (symB (symOf a b) = if a ≤ b then b else a)) 8) 8 = true := by
  refine ⟨by decide +kernel, by decide +kernel⟩

@[expose] public def symRow (k : Fin 36) : Fin 8 := ⟨symA k.val, symA_lt k.val⟩

@[expose] public def symCol (k : Fin 36) : Fin 8 := ⟨symB k.val, symB_lt k.val⟩

@[expose] public def symIdx (a b : Fin 8) : Fin 36 := ⟨symOf a.val b.val, symOf_lt a.val b.val⟩

/-- The coordinates of a symmetric matrix: its upper triangle, in the order
`symTab` lists it. -/
@[expose] public def symCoord (Y : Mat 8 8 Rat) : Vec 36 Rat := fun k => Y (symRow k) (symCol k)

/-- The symmetric matrix a coordinate vector names. -/
@[expose] public def symMat (c : Vec 36 Rat) : Mat 8 8 Rat := fun a b => c (symIdx a b)

public theorem symOf_spec (a b : Fin 8) :
    symA (symOf a.val b.val) = (if a.val ≤ b.val then a.val else b.val)
      ∧ symB (symOf a.val b.val) = (if a.val ≤ b.val then b.val else a.val) := by
  have h := allLt_true _ _ (allLt_true _ _ symComp.2 a.val a.isLt) b.val b.isLt
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

/-- `symMat` is symmetric by construction. -/
public theorem symMat_symm (c : Vec 36 Rat) (a b : Fin 8) : symMat c a b = symMat c b a := by
  show c (symIdx a b) = c (symIdx b a)
  refine congrArg c (Fin.eq_of_val_eq ?_)
  show symOf a.val b.val = symOf b.val a.val
  have h1 := symOf_spec a b
  have h2 := symOf_spec b a
  have hk1 := allLt_true _ _ symComp.1 (symOf a.val b.val) (symOf_lt a.val b.val)
  have hk2 := allLt_true _ _ symComp.1 (symOf b.val a.val) (symOf_lt b.val a.val)
  have e1 : symOf (symA (symOf a.val b.val)) (symB (symOf a.val b.val)) = symOf a.val b.val :=
    of_decide_eq_true hk1
  have e2 : symOf (symA (symOf b.val a.val)) (symB (symOf b.val a.val)) = symOf b.val a.val :=
    of_decide_eq_true hk2
  rw [← e1, ← e2, h1.1, h1.2, h2.1, h2.2]
  by_cases h : a.val ≤ b.val
  · rw [if_pos h, if_pos h]
    by_cases h' : b.val ≤ a.val
    · rw [if_pos h', if_pos h', show a.val = b.val from Nat.le_antisymm h h']
    · rw [if_neg h', if_neg h']
  · rw [if_neg h, if_neg h, if_pos (show b.val ≤ a.val by omega), if_pos (show b.val ≤ a.val by omega)]

/-- The two maps are mutually inverse: `Sym^2(Q^O)` has dimension `36`. -/
public theorem symMat_coord {Y : Mat 8 8 Rat} (hY : ∀ a b : Fin 8, Y a b = Y b a) (a b : Fin 8) :
    symMat (symCoord Y) a b = Y a b := by
  show Y (symRow (symIdx a b)) (symCol (symIdx a b)) = Y a b
  obtain ⟨h1, h2⟩ := symOf_spec a b
  have hr : (symRow (symIdx a b)).val = symA (symOf a.val b.val) := rfl
  have hc : (symCol (symIdx a b)).val = symB (symOf a.val b.val) := rfl
  by_cases h : a.val ≤ b.val
  · rw [h1, if_pos h] at hr
    rw [h2, if_pos h] at hc
    rw [Fin.eq_of_val_eq hr, Fin.eq_of_val_eq hc]
  · rw [h1, if_neg h] at hr
    rw [h2, if_neg h] at hc
    rw [Fin.eq_of_val_eq hr, Fin.eq_of_val_eq hc]
    exact hY b a

public theorem symCoord_mat (c : Vec 36 Rat) (k : Fin 36) : symCoord (symMat c) k = c k := by
  show c (symIdx (symRow k) (symCol k)) = c k
  refine congrArg c (Fin.eq_of_val_eq ?_)
  show symOf (symA k.val) (symB k.val) = k.val
  exact of_decide_eq_true (allLt_true _ _ symComp.1 k.val k.isLt)

/-! ## `S39`, `S40`: the isometry representation on `Sym^2`, and its commutant

The group layer is being written concurrently and is not importable here, so
the certified generating set of `Gauge(W)` and its order `4608` enter as
parameters: what is proved below is that *any* linear isometry of `Q^O` acts on
`Sym^2(Q^O)` by conjugation, that the action is a representation, that it is
insensitive to one global sign -- the ambiguity `T73` leaves in the lift -- and
that `S_X` commutes with it whenever the induced permutation of the classes
preserves `X`. -/

/-- The conjugation action `Y |-> g Y g^T` of a linear map on `8 x 8`
matrices. -/
@[expose] public def conjQ (g Y : Mat 8 8 Rat) : Mat 8 8 Rat :=
  Mat.mul (Mat.mul g Y) (Mat.transpose g)

/-- A linear isometry of `Q^O`: an orthogonal matrix over `Q`. -/
@[expose] public def IsoQ (g : Mat 8 8 Rat) : Prop :=
  Mat.mul (Mat.transpose g) g = (Mat.id : Mat 8 8 Rat)
    ∧ Mat.mul g (Mat.transpose g) = (Mat.id : Mat 8 8 Rat)

public theorem conjQ_mul (g h Y : Mat 8 8 Rat) :
    conjQ (Mat.mul g h) Y = conjQ g (conjQ h Y) := by
  show Mat.mul (Mat.mul (Mat.mul g h) Y) (Mat.transpose (Mat.mul g h))
    = Mat.mul (Mat.mul g (Mat.mul (Mat.mul h Y) (Mat.transpose h))) (Mat.transpose g)
  rw [Mat.transpose_mul g h, M2 g h Y, M2 g (Mat.mul h Y) (Mat.mul (Mat.transpose h)
      (Mat.transpose g)), ← M2 (Mat.mul h Y) (Mat.transpose h) (Mat.transpose g),
    M2 g (Mat.mul (Mat.mul h Y) (Mat.transpose h)) (Mat.transpose g)]

public theorem conjQ_id (Y : Mat 8 8 Rat) : conjQ (Mat.id : Mat 8 8 Rat) Y = Y := by
  show Mat.mul (Mat.mul Mat.id Y) (Mat.transpose (Mat.id : Mat 8 8 Rat)) = Y
  have ht : Mat.transpose (Mat.id : Mat 8 8 Rat) = Mat.id := by
    funext i j
    show (if j = i then (1 : Rat) else 0) = (if i = j then (1 : Rat) else 0)
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [ht, (M3 Y).1, (M3 Y).2]

public theorem neg_neg_rat (x : Rat) : neg (neg x) = x := Rat.neg_neg x

public theorem mul_neg_right (x y : Rat) : mul x (neg y) = neg (mul x y) := by
  rw [mul_comm x (neg y), neg_mul, mul_comm y x]

public theorem mul3_swap (x y z : Rat) : mul (mul x y) z = mul (mul z y) x := by
  have h1 : mul (mul x y) z = mul x (mul y z) := mul_assoc x y z
  have h2 : mul (mul z y) x = mul z (mul y x) := mul_assoc z y x
  rw [h1, h2, mul_comm y z, mul_comm y x, ← mul_assoc, ← mul_assoc, mul_comm x z]

/-- Cyclicity of the trace over `Q`. -/
public theorem traceQ_comm {n : Nat} (M N : Mat n n Rat) :
    traceQ (Mat.mul M N) = traceQ (Mat.mul N M) := by
  show Vec.sum (fun i : Fin n => Vec.sum (fun k : Fin n => mul (M i k) (N k i)))
    = Vec.sum (fun k : Fin n => Vec.sum (fun i : Fin n => mul (N k i) (M i k)))
  rw [Vec.sum_exchange (fun i k => mul (M i k) (N k i))]
  exact Vec.sum_congr (fun k => Vec.sum_congr (fun i => mul_comm (M i k) (N k i)))

public theorem conjQ_neg (g Y : Mat 8 8 Rat) (a b : Fin 8) :
    conjQ (Mat.neg g) Y a b = conjQ g Y a b := by
  have hrow : ∀ q : Fin 8, Mat.mul (Mat.neg g) Y a q = neg (Mat.mul g Y a q) := by
    intro q
    show Vec.sum (fun p : Fin 8 => mul (neg (g a p)) (Y p q))
      = neg (Vec.sum (fun p : Fin 8 => mul (g a p) (Y p q)))
    rw [← Vec.sum_neg]
    exact Vec.sum_congr (fun p => neg_mul (g a p) (Y p q))
  show Vec.sum (fun q : Fin 8 => mul (Mat.mul (Mat.neg g) Y a q) (neg (g b q)))
    = Vec.sum (fun q : Fin 8 => mul (Mat.mul g Y a q) (g b q))
  refine Vec.sum_congr (fun q => ?_)
  rw [hrow q, neg_mul, mul_neg_right, neg_neg_rat]

public theorem conjQ_symm {g Y : Mat 8 8 Rat} (hY : ∀ p q : Fin 8, Y p q = Y q p) (a b : Fin 8) :
    conjQ g Y a b = conjQ g Y b a := by
  have hexp : ∀ x y : Fin 8, conjQ g Y x y
      = Vec.sum (fun q : Fin 8 => Vec.sum (fun p : Fin 8 => mul (mul (g x p) (Y p q)) (g y q))) := by
    intro x y
    show Vec.sum (fun q : Fin 8 => mul (Vec.sum (fun p : Fin 8 => mul (g x p) (Y p q))) (g y q)) = _
    exact Vec.sum_congr (fun q => Vec.sum_mul _ _)
  rw [hexp a b, hexp b a, Vec.sum_exchange (fun q p => mul (mul (g a p) (Y p q)) (g b q))]
  refine Vec.sum_congr (fun i => Vec.sum_congr (fun j => ?_))
  rw [hY j i]
  exact mul3_swap (g a i) (Y i j) (g b j)

/-- `S39`. A linear isometry of `Q^O` acts on `Sym^2(Q^O)` by conjugation, and
the action is a representation: it is multiplicative, unital, insensitive to the
global sign that `T73` leaves free in the lift, and it preserves symmetry. The
space it acts on has dimension `36`, exhibited by the mutually inverse
coordinate maps `symCoord` and `symMat`.

The generating set of `Gauge(W)` and its order `4608` are the parameters here:
the group layer is not importable from this module, so `g` and `h` range over
arbitrary isometries rather than over a certified generating set. -/
public theorem S39 (g h Y : Mat 8 8 Rat) :
    conjQ (Mat.mul g h) Y = conjQ g (conjQ h Y)
      ∧ conjQ (Mat.id : Mat 8 8 Rat) Y = Y
      ∧ (∀ a b : Fin 8, conjQ (Mat.neg g) Y a b = conjQ g Y a b)
      ∧ ((∀ p q : Fin 8, Y p q = Y q p) → ∀ a b : Fin 8, conjQ g Y a b = conjQ g Y b a)
      ∧ (∀ c : Vec 36 Rat, ∀ a b : Fin 8, symMat c a b = symMat c b a)
      ∧ (∀ c : Vec 36 Rat, ∀ k : Fin 36, symCoord (symMat c) k = c k)
      ∧ (∀ Z : Mat 8 8 Rat, (∀ p q : Fin 8, Z p q = Z q p) →
          ∀ a b : Fin 8, symMat (symCoord Z) a b = Z a b) :=
  ⟨conjQ_mul g h Y, conjQ_id Y, conjQ_neg g Y, fun hY => conjQ_symm hY,
    symMat_symm, symCoord_mat, fun _ hZ => symMat_coord hZ⟩

/-! ### `S40`: `S_X` commutes with the representation -/

/-- A sum over a permuted index set. -/
public theorem sum_reindexQ {n : Nat} (σ τ : Fin n → Fin n)
    (hτσ : ∀ i, τ (σ i) = i) (hστ : ∀ j, σ (τ j) = j) (f : Fin n → Rat) :
    Vec.sum (fun i => f (σ i)) = Vec.sum f := by
  have h1 : ∀ i : Fin n, f (σ i) = Vec.sum (fun j => if j = σ i then f j else zero) :=
    fun i => (Vec.sum_ite_eq' (σ i) f).symm
  rw [Vec.sum_congr h1, Vec.sum_exchange (fun i j => if j = σ i then f j else zero)]
  refine Vec.sum_congr (fun j => ?_)
  have h2 : ∀ i : Fin n, (if j = σ i then f j else zero) = (if i = τ j then f j else zero) := by
    intro i
    by_cases h : i = τ j
    · rw [if_pos h, if_pos (by rw [h, hστ])]
    · rw [if_neg h, if_neg (fun hh => h ((congrArg τ hh).trans (hτσ i)).symm)]
  rw [Vec.sum_congr h2]
  exact Vec.sum_ite_eq' (τ j) (fun _ => f j)

public theorem conjQ_zero (g : Mat 8 8 Rat) (a b : Fin 8) :
    conjQ g (fun _ _ => zero) a b = zero := by
  have hrow : ∀ q : Fin 8, Mat.mul g (fun _ _ => (zero : Rat)) a q = zero := by
    intro q
    show Vec.sum (fun p : Fin 8 => mul (g a p) zero) = zero
    rw [Vec.sum_congr (y := fun _ => zero) (fun p => mul_zero (g a p))]
    exact Vec.sum_zero
  show Vec.sum (fun q : Fin 8 => mul (Mat.mul g (fun _ _ => (zero : Rat)) a q) (g b q)) = zero
  rw [Vec.sum_congr (y := fun _ => zero) (fun q => by rw [hrow q]; exact zero_mul (g b q))]
  exact Vec.sum_zero

public theorem conjQ_smul (g P : Mat 8 8 Rat) (c : Rat) (a b : Fin 8) :
    conjQ g (fun p q => mul c (P p q)) a b = mul c (conjQ g P a b) := by
  have hrow : ∀ q : Fin 8, Mat.mul g (fun p q => mul c (P p q)) a q
      = mul c (Mat.mul g P a q) := by
    intro q
    show Vec.sum (fun p : Fin 8 => mul (g a p) (mul c (P p q)))
      = mul c (Vec.sum (fun p : Fin 8 => mul (g a p) (P p q)))
    rw [Vec.mul_sum]
    exact Vec.sum_congr (fun p => by
      rw [← mul_assoc, ← mul_assoc, mul_comm (g a p) c])
  show Vec.sum (fun q : Fin 8 => mul (Mat.mul g (fun p q => mul c (P p q)) a q) (g b q))
    = mul c (Vec.sum (fun q : Fin 8 => mul (Mat.mul g P a q) (g b q)))
  rw [Vec.mul_sum]
  exact Vec.sum_congr (fun q => by rw [hrow q, mul_assoc])

public theorem conjQ_sumK (g : Mat 8 8 Rat) (G : K → Mat 8 8 Rat) (a b : Fin 8) :
    conjQ g (fun p q => Vec.sum (fun v : K => G v p q)) a b
      = Vec.sum (fun v : K => conjQ g (G v) a b) := by
  have hrow : ∀ q : Fin 8, Mat.mul g (fun p q => Vec.sum (fun v : K => G v p q)) a q
      = Vec.sum (fun v : K => Mat.mul g (G v) a q) := by
    intro q
    show Vec.sum (fun p : Fin 8 => mul (g a p) (Vec.sum (fun v : K => G v p q)))
      = Vec.sum (fun v : K => Vec.sum (fun p : Fin 8 => mul (g a p) (G v p q)))
    rw [Vec.sum_congr (fun p => Vec.mul_sum (g a p) (fun v : K => G v p q))]
    exact Vec.sum_exchange (fun p (v : K) => mul (g a p) (G v p q))
  have hstep : ∀ q : Fin 8,
      mul (Mat.mul g (fun p q => Vec.sum (fun v : K => G v p q)) a q) (g b q)
        = Vec.sum (fun v : K => mul (Mat.mul g (G v) a q) (g b q)) := by
    intro q
    rw [hrow q]
    exact Vec.sum_mul (fun v : K => Mat.mul g (G v) a q) (g b q)
  show Vec.sum (fun q : Fin 8 =>
      mul (Mat.mul g (fun p q => Vec.sum (fun v : K => G v p q)) a q) (g b q))
    = Vec.sum (fun v : K => Vec.sum (fun q : Fin 8 => mul (Mat.mul g (G v) a q) (g b q)))
  rw [Vec.sum_congr hstep]
  exact Vec.sum_exchange (fun (q : Fin 8) (v : K) => mul (Mat.mul g (G v) a q) (g b q))

/-- The trace form is insensitive to conjugating both arguments by an
isometry. -/
public theorem traceQ_conjQ {g : Mat 8 8 Rat} (hg : IsoQ g) (P Y : Mat 8 8 Rat) :
    traceQ (Mat.mul (conjQ g P) (conjQ g Y)) = traceQ (Mat.mul P Y) := by
  show traceQ (Mat.mul (Mat.mul (Mat.mul g P) (Mat.transpose g))
      (Mat.mul (Mat.mul g Y) (Mat.transpose g))) = _
  rw [M2 (Mat.mul g P) (Mat.transpose g) (Mat.mul (Mat.mul g Y) (Mat.transpose g)),
    ← M2 (Mat.transpose g) (Mat.mul g Y) (Mat.transpose g),
    ← M2 (Mat.transpose g) g Y, hg.1, (M3 Y).1,
    traceQ_comm (Mat.mul g P) (Mat.mul Y (Mat.transpose g)),
    M2 Y (Mat.transpose g) (Mat.mul g P),
    ← M2 (Mat.transpose g) g P, hg.1, (M3 P).1,
    traceQ_comm Y P]

/-- `qsumN` and a sum over `K` are the same sum: the bridge `D61`'s `Nat`-indexed
form needs before a permutation of the classes can be applied to it. -/
public theorem qsumN_front (f : Nat → Rat) :
    ∀ m, f 0 + qsumN (fun j => f (j + 1)) m = qsumN f (m + 1) := by
  intro m
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [qsumN_succ, qsumN_succ (f := f), ← ih, ← Rat.add_assoc, ← Rat.add_assoc,
      Rat.add_comm (f 0) (f (n + 1))]

public theorem qsumN_eq_vecsum : ∀ (m : Nat) (f : Nat → Rat),
    Vec.sum (n := m) (fun k : Fin m => f k.val) = qsumN f m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ n ih =>
    intro f
    show f 0 + Vec.sum (fun i : Fin n => f (Fin.succ i).val) = qsumN f (n + 1)
    have h : ∀ i : Fin n, f (Fin.succ i).val = f (i.val + 1) := fun i => rfl
    rw [Vec.sum_congr h, ih (fun j => f (j + 1)), qsumN_front]

public theorem D61_vecsum (W : Bitset) (Y : Mat 8 8 Rat) (a b : Fin 8) :
    D61 W Y a b = Vec.sum (fun u : K =>
      if u.val ∈ W then mul (traceQ (Mat.mul (projQ u) Y)) (projQ u a b) else zero) := by
  show qsumN (fun u => if u ∈ W then
      traceQ (Mat.mul (projQ (kOf u)) Y) * projQ (kOf u) a b else 0) 120 = _
  rw [← qsumN_eq_vecsum 120 (fun u => if u ∈ W then
      traceQ (Mat.mul (projQ (kOf u)) Y) * projQ (kOf u) a b else 0)]
  refine Vec.sum_congr (fun u => ?_)
  have hk : kOf u.val = u := Fin.eq_of_val_eq (Nat.mod_eq_of_lt u.isLt)
  rw [hk]
  exact rfl

/-- `S40`. `S_X` commutes with the representation of `S39`: if the isometry `g`
carries the projection of every class `u` to the projection of `sigma u`, and
`sigma` is a permutation of the classes preserving `X`, then
`S_X(g Y g^T) = g S_X(Y) g^T`. The AtlasInstance instance of this is `S40` for
`Gauge(W)`; which permutation `sigma` a generator of the gauge group induces is
a fact of the group layer, and is a parameter here for the same reason `S39`'s
generating set is. -/
public theorem S40 {W : Bitset} {g : Mat 8 8 Rat} {σ τ : K → K} (hg : IsoQ g)
    (hτσ : ∀ u, τ (σ u) = u) (hστ : ∀ u, σ (τ u) = u)
    (hW : ∀ u : K, ((σ u).val ∈ W) = (u.val ∈ W))
    (hP : ∀ u : K, conjQ g (projQ u) = projQ (σ u))
    (Y : Mat 8 8 Rat) (a b : Fin 8) :
    D61 W (conjQ g Y) a b = conjQ g (D61 W Y) a b := by
  have hstep : ∀ v : K,
      (if (σ v).val ∈ W then mul (traceQ (Mat.mul (projQ (σ v)) (conjQ g Y)))
          (projQ (σ v) a b) else zero)
        = conjQ g (fun p q => if v.val ∈ W then mul (traceQ (Mat.mul (projQ v) Y))
            (projQ v p q) else zero) a b := by
    intro v
    by_cases h : v.val ∈ W
    · rw [if_pos (by rw [hW v]; exact h)]
      have hfun : (fun p q => if v.val ∈ W then mul (traceQ (Mat.mul (projQ v) Y))
          (projQ v p q) else zero)
          = (fun p q => mul (traceQ (Mat.mul (projQ v) Y)) (projQ v p q)) := by
        funext p q; rw [if_pos h]
      rw [hfun, conjQ_smul g (projQ v) (traceQ (Mat.mul (projQ v) Y)) a b, ← hP v,
        traceQ_conjQ hg (projQ v) Y]
    · rw [if_neg (by rw [hW v]; exact h)]
      have hfun : (fun p q => if v.val ∈ W then mul (traceQ (Mat.mul (projQ v) Y))
          (projQ v p q) else zero) = (fun _ _ => (zero : Rat)) := by
        funext p q; rw [if_neg h]
      rw [hfun, conjQ_zero g a b]
  have hmat : D61 W Y = fun p q => Vec.sum (fun v : K =>
      if v.val ∈ W then mul (traceQ (Mat.mul (projQ v) Y)) (projQ v p q) else zero) :=
    funext fun p => funext fun q => D61_vecsum W Y p q
  rw [D61_vecsum W (conjQ g Y) a b, hmat,
    ← sum_reindexQ σ τ hτσ hστ (fun u : K => if u.val ∈ W
      then mul (traceQ (Mat.mul (projQ u) (conjQ g Y))) (projQ u a b) else zero),
    Vec.sum_congr hstep]
  exact (conjQ_sumK g (fun v => fun p q => if v.val ∈ W
    then mul (traceQ (Mat.mul (projQ v) Y)) (projQ v p q) else zero) a b).symm


/-! ## `S33`, `S34`, `S35`, `S36`: section 17.6, the frame operator and
its spectrum

Section 17.6 relates three objects: the class graph `A_X`, the Gram matrix
`M_X = [tr(P_i P_j)]` of the projections in the trace form, and the frame
operator `S_X` of `D61` on `Sym^2(Q^O)`. One map carries all of it, the
"synthesis" map `W_X : Q^X -> Sym^2(Q^O)`, `c |-> sum_i c_i P_i` (`projComb`),
together with its adjoint in the trace form, `W_X^* : Y |-> (tr(P_i Y))_i`
(`projCoef`). Exactly, and with no hypothesis: `M_X = W_X^* W_X`
(`projCoef_projComb`) and `S_X = W_X W_X^*` (`frameOpL_eq`).

No eigenvalue is an object of this library, so "`mu` lies in the spectrum" is
read as "there is a nonzero eigenvector at `mu`", exactly as `D56` reads a
spectrum through an annihilating polynomial and integer traces. "The two
spectra agree" is then not an equality of lists but a pair of mutually inverse
linear maps between the two eigenspaces, `c |-> W_X c` and `Y |-> mu^-1 W_X^* Y`;
that is strictly stronger than equality of eigenvalue sets, because it carries
the multiplicities too, and it is what `S33` proves.

The ambient statement `S34` runs on a different mechanism: the operator `S_X`
is determined by the fourth moment tensor `sum_{i in X} r_a r_b r_c r_d` of the
representatives (`D61_expand`), and over all `120` classes that tensor is
exactly `96` times the symmetriser `d_ab d_cd + d_ac d_bd + d_ad d_bc`. That
single finite identity -- the spherical `4`-design property of the root system,
checked in eight windows so the kernel releases memory between them -- is the
whole of `S34`, and `S35` and `S36` are read off it.

`S37` below assembles this correspondence with the exact five-scale
multiplicity ledger of `S15`. `S32` uniquely pins those multiplicities from
annihilating polynomials and traces, while `xHasRank` supplies a split rank
certificate for the AtlasInstance eigenspace.
-/

/-- Cancelling the `64` that clearing the two `1/8`s of a product `P_i . P_j`
leaves. The companion of `rat_cancel16`. -/
public theorem rat_cancel64 {a b : Rat} (h : 64 * a = 64 * b) : a = b := by
  have h1 : (64 : Rat)⁻¹ * (64 * a) = (64 : Rat)⁻¹ * (64 * b) := by rw [h]
  rw [← Rat.mul_assoc, ← Rat.mul_assoc, Rat.inv_mul_cancel 64 (by decide),
    Rat.one_mul, Rat.one_mul] at h1
  exact h1

/-- `Vec.mul_sum` restated with `*` rather than `CommRing.mul`, so that `rw`
matches the shape the rational statements of this section are written in. The
three that follow do the same for `sum_mul`, `sum_add` and `sum_ite_eq`. -/
public theorem qmul_vsum {n : Nat} (r : Rat) (f : Vec n Rat) :
    r * Vec.sum f = Vec.sum (fun i => r * f i) := Vec.mul_sum r f

public theorem qvsum_mul {n : Nat} (f : Vec n Rat) (r : Rat) :
    Vec.sum f * r = Vec.sum (fun i => f i * r) := Vec.sum_mul f r

public theorem qvsum_add {n : Nat} (f g : Vec n Rat) :
    Vec.sum (fun i => f i + g i) = Vec.sum f + Vec.sum g := Vec.sum_add f g

public theorem qvsum_zero {n : Nat} : Vec.sum (fun _ : Fin n => (0 : Rat)) = 0 :=
  Vec.sum_zero

public theorem qvsum_ite_eq {n : Nat} (i : Fin n) (f : Vec n Rat) :
    Vec.sum (fun k : Fin n => if i = k then f k else (0 : Rat)) = f i := Vec.sum_ite_eq i f

public theorem qsumN_addFun (f g : Nat → Rat) : ∀ m,
    qsumN (fun k => f k + g k) m = qsumN f m + qsumN g m := by
  intro m
  induction m with
  | zero => exact (Rat.add_zero 0).symm
  | succ p ih => rw [qsumN_succ, qsumN_succ (f := f), qsumN_succ (f := g), ih]; grind

/-- Exchanging the `120`-fold `qsumN` of `D61` with a sum over coordinates.
The two run over different index types, so `Vec.sum_exchange` does not apply
and the induction is done directly. -/
public theorem qsumN_vsum {n : Nat} (F : Nat → Vec n Rat) : ∀ m,
    qsumN (fun u => Vec.sum (F u)) m = Vec.sum (fun c : Fin n => qsumN (fun u => F u c) m) := by
  intro m
  induction m with
  | zero => exact qvsum_zero.symm
  | succ p ih =>
    rw [qsumN_succ, ih]
    exact (qvsum_add (F p) (fun c => qsumN (fun u => F u c) p)).symm

public theorem qsumN_intCast (g : Nat → Int) : ∀ m,
    qsumN (fun k => ((g k : Int) : Rat)) m = ((isumN g m : Int) : Rat) := by
  intro m
  induction m with
  | zero => exact Rat.intCast_zero.symm
  | succ p ih => rw [qsumN_succ, ih, isumN_succ, Rat.intCast_add]

public theorem qsumN_cast_mul (g : Nat → Int) (z : Rat) : ∀ m,
    qsumN (fun u => ((g u : Int) : Rat) * z) m = ((isumN g m : Int) : Rat) * z := by
  intro m
  induction m with
  | zero =>
    show (0 : Rat) = ((0 : Int) : Rat) * z
    rw [Rat.intCast_zero, Rat.zero_mul]
  | succ p ih => rw [qsumN_succ, ih, isumN_succ, Rat.intCast_add]; grind

public theorem vsum_cast {m : Nat} (g : Vec m Int) :
    Vec.sum (fun i : Fin m => ((g i : Int) : Rat)) = ((Vec.sumInt g : Int) : Rat) := by
  rw [Vec.sumInt_eq_sum]
  exact (hom_map_sum intToRat g).symm

public theorem vsum_cast_mul {m : Nat} (g : Vec m Int) (z : Rat) :
    Vec.sum (fun i : Fin m => ((g i : Int) : Rat) * z) = ((Vec.sumInt g : Int) : Rat) * z := by
  rw [← qvsum_mul (fun i : Fin m => ((g i : Int) : Rat)) z, vsum_cast]

/-- `exch2` over `Q`: a class index outside, two coordinate indices inside. -/
public theorem qexch2 {m : Nat} (F : Fin m → Fin 8 → Fin 8 → Rat) :
    Vec.sum (fun i : Fin m => Vec.sum (fun c : Fin 8 => Vec.sum (fun d : Fin 8 => F i c d)))
      = Vec.sum (fun c : Fin 8 =>
          Vec.sum (fun d : Fin 8 => Vec.sum (fun i : Fin m => F i c d))) := by
  rw [Vec.sum_exchange (fun (i : Fin m) (c : Fin 8) => Vec.sum (fun d : Fin 8 => F i c d))]
  exact Vec.sum_congr (fun c => Vec.sum_exchange (fun (i : Fin m) (d : Fin 8) => F i c d))

/-- Below `120` the wrap-around in `kOf` is inert. -/
public theorem rep_kOf {k : Nat} (hk : k < 120) : rep (kOf k) = repN k :=
  congrArg repN (Nat.mod_eq_of_lt hk)

/-- The identity matrix over `Z` casts to the identity matrix over `Q`. -/
public theorem intCast_matId {n : Nat} (i j : Fin n) :
    (((Mat.id : Mat n n Int) i j : Int) : Rat) = (Mat.id : Mat n n Rat) i j := by
  show (((if i = j then (1 : Int) else 0) : Int) : Rat) = (if i = j then (1 : Rat) else 0)
  by_cases h : i = j
  · rw [if_pos h, if_pos h]; exact Rat.intCast_one
  · rw [if_neg h, if_neg h]; exact Rat.intCast_zero

/-- Multiplying by an entry of the identity is the indicator. -/
public theorem qite_mul {n : Nat} (i j : Fin n) (z : Rat) :
    (Mat.id : Mat n n Rat) i j * z = if i = j then z else 0 := by
  show (if i = j then (1 : Rat) else 0) * z = _
  by_cases h : i = j
  · rw [if_pos h, if_pos h, Rat.one_mul]
  · rw [if_neg h, if_neg h, Rat.zero_mul]

public theorem q4_cancel (z : Rat) : (4 : Rat) * ((4 : Rat)⁻¹ * z) = z := by
  rw [← Rat.mul_assoc, Rat.mul_inv_cancel 4 (by decide), Rat.one_mul]

public theorem q4_cancel' (z : Rat) : (4 : Rat)⁻¹ * ((4 : Rat) * z) = z := by
  rw [← Rat.mul_assoc, Rat.inv_mul_cancel 4 (by decide), Rat.one_mul]

/-! ### `W_X`, its adjoint, `M_X` and `S_X` on a listing

A class set `X` enters section 17.6 through an injective listing `x`, the same
presentation `D55`, `S13` and `S14` already use. `frameOpL` is `D61` written on
such a listing; `D61_atl_eq` identifies the two at the AtlasInstance. -/

/-- `W_X`, the synthesis map of the class set listed by `x`:
`c |-> sum_i c_i P_i`, an element of `Sym^2(Q^O)`. `gramComb` is `8 W_X` on
integer coefficients and unscaled `r_i r_i^T`. -/
@[expose] public def projComb {m : Nat} (x : Fin m → K) (c : Vec m Rat) : Mat 8 8 Rat :=
  fun a b => Vec.sum (fun i : Fin m => c i * projQ (x i) a b)

/-- `W_X^*`, the adjoint of `projComb` in the trace form: the analysis map
`Y |-> (tr(P_i Y))_i`. -/
@[expose] public def projCoef {m : Nat} (x : Fin m → K) (Y : Mat 8 8 Rat) : Vec m Rat :=
  fun i => traceQ (Mat.mul (projQ (x i)) Y)

/-- `M_X = [tr(P_i P_j)]`, the Gram matrix of the projections of `X` in the
trace form, over `Q`. `D55` is `16 M_X` over `Z`. -/
@[expose] public def projGramQ {m : Nat} (x : Fin m → K) : Mat m m Rat :=
  fun i j => traceQ (Mat.mul (projQ (x i)) (projQ (x j)))

/-- `S_X` written on a listing of `X` rather than on its bitset: the sum of
`D61` taken along `x`. -/
@[expose] public def frameOpL {m : Nat} (x : Fin m → K) (Y : Mat 8 8 Rat) : Mat 8 8 Rat :=
  fun a b => Vec.sum (fun i : Fin m => traceQ (Mat.mul (projQ (x i)) Y) * projQ (x i) a b)

/-- `S_X = W_X W_X^*`, on the nose. -/
public theorem frameOpL_eq {m : Nat} (x : Fin m → K) (Y : Mat 8 8 Rat) (a b : Fin 8) :
    frameOpL x Y a b = projComb x (projCoef x Y) a b := rfl

/-! ### the fourth moment tensor

`S_X` is determined by `sum_{i in X} r_a r_b r_c r_d`: expanding
`tr(P_i Y) P_i` gives `(1/64) sum_{c,d} (r_a r_b r_c r_d) Y_dc`, so two class
sets with the same fourth moment carry the same frame operator. That is what
makes `S34` a single finite identity and what bridges the bitset form `D61` to
the listing form `frameOpL`. -/

@[expose] public def mom4B (W : Bitset) (a b c d : Fin 8) : Int :=
  isumN (fun u => if u ∈ W then repN u a * repN u b * (repN u c * repN u d) else 0) 120

@[expose] public def mom4L {m : Nat} (x : Fin m → K) (a b c d : Fin 8) : Int :=
  Vec.sumInt (fun i : Fin m => rep (x i) a * rep (x i) b * (rep (x i) c * rep (x i) d))

public theorem traceQ_mul_expand (M N : Mat 8 8 Rat) :
    traceQ (Mat.mul M N)
      = Vec.sum (fun c : Fin 8 => Vec.sum (fun d : Fin 8 => M c d * N d c)) :=
  Vec.sum_congr (fun c => Mat.mul_apply M N c c)

public theorem eight_projQ (v : K) (a b : Fin 8) :
    ((8 : Int) : Rat) * projQ v a b = ((rep v a * rep v b : Int) : Rat) := by
  show ((8 : Int) : Rat) * ((8 : Rat)⁻¹ * ((rep v a * rep v b : Int) : Rat)) = _
  exact inv8_cancel' _

public theorem eight_trace_projQ (v : K) (Y : Mat 8 8 Rat) :
    ((8 : Int) : Rat) * traceQ (Mat.mul (projQ v) Y)
      = Vec.sum (fun c : Fin 8 => Vec.sum (fun d : Fin 8 =>
          ((rep v c * rep v d : Int) : Rat) * Y d c)) := by
  rw [traceQ_mul_expand, qmul_vsum]
  refine Vec.sum_congr (fun c => ?_)
  rw [qmul_vsum]
  refine Vec.sum_congr (fun d => ?_)
  rw [← Rat.mul_assoc, eight_projQ v c d]

/-- One term of the frame operator, with both denominators cleared. -/
public theorem projQ_term_expand (v : K) (Y : Mat 8 8 Rat) (a b : Fin 8) :
    (64 : Rat) * (traceQ (Mat.mul (projQ v) Y) * projQ v a b)
      = Vec.sum (fun c : Fin 8 => Vec.sum (fun d : Fin 8 =>
          ((rep v a * rep v b * (rep v c * rep v d) : Int) : Rat) * Y d c)) := by
  have h64 : (64 : Rat) = ((8 : Int) : Rat) * ((8 : Int) : Rat) := by decide +kernel
  have hkey : (64 : Rat) * (traceQ (Mat.mul (projQ v) Y) * projQ v a b)
      = (((8 : Int) : Rat) * traceQ (Mat.mul (projQ v) Y))
        * (((8 : Int) : Rat) * projQ v a b) := by
    rw [h64]; grind
  rw [hkey, eight_trace_projQ v Y, eight_projQ v a b, qvsum_mul]
  refine Vec.sum_congr (fun c => ?_)
  rw [qvsum_mul]
  refine Vec.sum_congr (fun d => ?_)
  rw [Rat.intCast_mul (rep v a * rep v b) (rep v c * rep v d)]
  grind

/-- `S_X` in terms of its fourth moment tensor, bitset form. -/
public theorem D61_expand (W : Bitset) (Y : Mat 8 8 Rat) (a b : Fin 8) :
    (64 : Rat) * D61 W Y a b
      = Vec.sum (fun c : Fin 8 => Vec.sum (fun d : Fin 8 =>
          ((mom4B W a b c d : Int) : Rat) * Y d c)) := by
  have hterm : ∀ k, k < 120 →
      (64 : Rat) * (if k ∈ W then traceQ (Mat.mul (projQ (kOf k)) Y) * projQ (kOf k) a b else 0)
        = Vec.sum (fun c : Fin 8 => Vec.sum (fun d : Fin 8 =>
            (((if k ∈ W then repN k a * repN k b * (repN k c * repN k d) else 0 : Int)
              : Int) : Rat) * Y d c)) := by
    intro k hk
    by_cases h : k ∈ W
    · rw [if_pos h, projQ_term_expand (kOf k) Y a b]
      refine Vec.sum_congr (fun c => Vec.sum_congr (fun d => ?_))
      rw [if_pos h, rep_kOf hk]
    · rw [if_neg h, Rat.mul_zero]
      have hz : ∀ c : Fin 8, Vec.sum (fun d : Fin 8 =>
          (((if k ∈ W then repN k a * repN k b * (repN k c * repN k d) else 0 : Int)
            : Int) : Rat) * Y d c) = 0 := by
        intro c
        have hd : ∀ d : Fin 8,
            (((if k ∈ W then repN k a * repN k b * (repN k c * repN k d) else 0 : Int)
              : Int) : Rat) * Y d c = (0 : Rat) := by
          intro d
          rw [if_neg h, Rat.intCast_zero, Rat.zero_mul]
        rw [Vec.sum_congr hd]
        exact qvsum_zero
      rw [Vec.sum_congr hz]
      exact qvsum_zero.symm
  show (64 : Rat) * qsumN (fun u => if u ∈ W then
      traceQ (Mat.mul (projQ (kOf u)) Y) * projQ (kOf u) a b else 0) 120 = _
  rw [qsumN_smul, qsumN_congr _ _ 120 hterm,
    qsumN_vsum (fun u => fun c : Fin 8 => Vec.sum (fun d : Fin 8 =>
      (((if u ∈ W then repN u a * repN u b * (repN u c * repN u d) else 0 : Int)
        : Int) : Rat) * Y d c)) 120]
  refine Vec.sum_congr (fun c => ?_)
  rw [qsumN_vsum (fun u => fun d : Fin 8 =>
      (((if u ∈ W then repN u a * repN u b * (repN u c * repN u d) else 0 : Int)
        : Int) : Rat) * Y d c) 120]
  refine Vec.sum_congr (fun d => ?_)
  exact qsumN_cast_mul _ (Y d c) 120

/-- `S_X` in terms of its fourth moment tensor, listing form. -/
public theorem frameOpL_expand {m : Nat} (x : Fin m → K) (Y : Mat 8 8 Rat) (a b : Fin 8) :
    (64 : Rat) * frameOpL x Y a b
      = Vec.sum (fun c : Fin 8 => Vec.sum (fun d : Fin 8 =>
          ((mom4L x a b c d : Int) : Rat) * Y d c)) := by
  show (64 : Rat) * Vec.sum (fun i : Fin m =>
      traceQ (Mat.mul (projQ (x i)) Y) * projQ (x i) a b) = _
  rw [qmul_vsum, Vec.sum_congr (fun i : Fin m => projQ_term_expand (x i) Y a b),
    qexch2 (fun (i : Fin m) (c : Fin 8) (d : Fin 8) =>
      ((rep (x i) a * rep (x i) b * (rep (x i) c * rep (x i) d) : Int) : Rat) * Y d c)]
  refine Vec.sum_congr (fun c => Vec.sum_congr (fun d => ?_))
  exact vsum_cast_mul _ (Y d c)

/-- The fourth moment tensor `S34` asserts for the ambient root system: `96`
times the symmetriser of `Sym^2`. -/
@[expose] public def mom4Amb (a b c d : Fin 8) : Int :=
  96 * ((Mat.id : Mat 8 8 Int) a b * (Mat.id : Mat 8 8 Int) c d
    + (Mat.id : Mat 8 8 Int) a c * (Mat.id : Mat 8 8 Int) b d
    + (Mat.id : Mat 8 8 Int) a d * (Mat.id : Mat 8 8 Int) b c)

/-- One window of the ambient check: `512` entries, each a `120`-term sum.
The `4096` entries are cut into eight declarations because the kernel releases
memory between declarations and not inside one. -/
@[expose] public def mom4AmbWin (a : Fin 8) : Bool :=
  allFin (fun b : Fin 8 => allFin (fun c : Fin 8 => allFin (fun d : Fin 8 =>
    decide (mom4B fullK a b c d = mom4Amb a b c d))))

/-- One window of the AtlasInstance bridge, cut for the same reason. -/
@[expose] public def mom4AtlWin (a : Fin 8) : Bool :=
  allFin (fun b : Fin 8 => allFin (fun c : Fin 8 => allFin (fun d : Fin 8 =>
    decide (mom4B atlSet a b c d = mom4L atlClass a b c d))))

public theorem ambWin0 : mom4AmbWin 0 = true := by decide +kernel
public theorem ambWin1 : mom4AmbWin 1 = true := by decide +kernel
public theorem ambWin2 : mom4AmbWin 2 = true := by decide +kernel
public theorem ambWin3 : mom4AmbWin 3 = true := by decide +kernel
public theorem ambWin4 : mom4AmbWin 4 = true := by decide +kernel
public theorem ambWin5 : mom4AmbWin 5 = true := by decide +kernel
public theorem ambWin6 : mom4AmbWin 6 = true := by decide +kernel
public theorem ambWin7 : mom4AmbWin 7 = true := by decide +kernel

public theorem atlWin0 : mom4AtlWin 0 = true := by decide +kernel
public theorem atlWin1 : mom4AtlWin 1 = true := by decide +kernel
public theorem atlWin2 : mom4AtlWin 2 = true := by decide +kernel
public theorem atlWin3 : mom4AtlWin 3 = true := by decide +kernel
public theorem atlWin4 : mom4AtlWin 4 = true := by decide +kernel
public theorem atlWin5 : mom4AtlWin 5 = true := by decide +kernel
public theorem atlWin6 : mom4AtlWin 6 = true := by decide +kernel
public theorem atlWin7 : mom4AtlWin 7 = true := by decide +kernel

/-- The spherical `4`-design identity of the `120` ambient classes, assembled
from its eight windows. -/
public theorem mom4_amb (a b c d : Fin 8) : mom4B fullK a b c d = mom4Amb a b c d := by
  have hall : ∀ e : Fin 8, mom4AmbWin e = true := by
    intro e
    match e with
    | ⟨0, _⟩ => exact ambWin0
    | ⟨1, _⟩ => exact ambWin1
    | ⟨2, _⟩ => exact ambWin2
    | ⟨3, _⟩ => exact ambWin3
    | ⟨4, _⟩ => exact ambWin4
    | ⟨5, _⟩ => exact ambWin5
    | ⟨6, _⟩ => exact ambWin6
    | ⟨7, _⟩ => exact ambWin7
  exact of_decide_eq_true
    (allFin_true _ (allFin_true _ (allFin_true _ (hall a) b) c) d)

/-- The listing `atlClass` and the bitset `atlSet` have the same fourth moment
tensor. `xClass_mem`, `xClass_onto` and `xClass_inj` say the listing is a
bijection onto the set; this is the numerical form of that fact which the
frame operator actually consumes. -/
public theorem mom4_atl (a b c d : Fin 8) : mom4B atlSet a b c d = mom4L atlClass a b c d := by
  have hall : ∀ e : Fin 8, mom4AtlWin e = true := by
    intro e
    match e with
    | ⟨0, _⟩ => exact atlWin0
    | ⟨1, _⟩ => exact atlWin1
    | ⟨2, _⟩ => exact atlWin2
    | ⟨3, _⟩ => exact atlWin3
    | ⟨4, _⟩ => exact atlWin4
    | ⟨5, _⟩ => exact atlWin5
    | ⟨6, _⟩ => exact atlWin6
    | ⟨7, _⟩ => exact atlWin7
  exact of_decide_eq_true
    (allFin_true _ (allFin_true _ (allFin_true _ (hall a) b) c) d)

/-- The frame operator of the AtlasInstance is the same whether it is summed
over the bitset `atlSet` or along the listing `atlClass`. This is what lets
`S33` and the top-eigenvalue bound, stated for a listing, be statements about
the `S_X` of `D61`. -/
public theorem D61_atl_eq (Y : Mat 8 8 Rat) (a b : Fin 8) :
    D61 atlSet Y a b = frameOpL atlClass Y a b := by
  refine rat_cancel64 ?_
  rw [D61_expand, frameOpL_expand]
  exact Vec.sum_congr (fun c => Vec.sum_congr (fun d => by rw [mom4_atl a b c d]))

/-! ### `S34`, `S35`, `S36` -/

public theorem mom4Amb_cast (a b c d : Fin 8) :
    ((mom4Amb a b c d : Int) : Rat)
      = 96 * ((Mat.id : Mat 8 8 Rat) a b * (Mat.id : Mat 8 8 Rat) c d
        + (Mat.id : Mat 8 8 Rat) a c * (Mat.id : Mat 8 8 Rat) b d
        + (Mat.id : Mat 8 8 Rat) a d * (Mat.id : Mat 8 8 Rat) b c) := by
  show ((96 * ((Mat.id : Mat 8 8 Int) a b * (Mat.id : Mat 8 8 Int) c d
      + (Mat.id : Mat 8 8 Int) a c * (Mat.id : Mat 8 8 Int) b d
      + (Mat.id : Mat 8 8 Int) a d * (Mat.id : Mat 8 8 Int) b c) : Int) : Rat) = _
  rw [Rat.intCast_mul, Rat.intCast_add, Rat.intCast_add, Rat.intCast_mul, Rat.intCast_mul,
    Rat.intCast_mul, intCast_matId, intCast_matId, intCast_matId, intCast_matId,
    intCast_matId, intCast_matId]
  rfl

/-- Contracting the ambient fourth moment tensor against a matrix. The three
summands of the symmetriser give the trace term and the two transposes; only
after the symmetry of `Y` do the transposes merge, which is exactly why `S34`
is a statement about `Sym^2` and not about all of `M_8(Q)`. -/
public theorem S34_sum (Y : Mat 8 8 Rat) (a b : Fin 8) :
    Vec.sum (fun c : Fin 8 => Vec.sum (fun d : Fin 8 =>
        ((mom4B fullK a b c d : Int) : Rat) * Y d c))
      = 96 * (Mat.id : Mat 8 8 Rat) a b * traceQ Y + (96 * Y b a + 96 * Y a b) := by
  have hinner : ∀ c : Fin 8, Vec.sum (fun d : Fin 8 =>
      ((mom4B fullK a b c d : Int) : Rat) * Y d c)
      = 96 * (Mat.id : Mat 8 8 Rat) a b * Y c c
        + (96 * (Mat.id : Mat 8 8 Rat) a c * Y b c
          + 96 * (Mat.id : Mat 8 8 Rat) b c * Y a c) := by
    intro c
    have hd : ∀ d : Fin 8, ((mom4B fullK a b c d : Int) : Rat) * Y d c
        = 96 * (Mat.id : Mat 8 8 Rat) a b * (if c = d then Y d c else 0)
          + (96 * (Mat.id : Mat 8 8 Rat) a c * (if b = d then Y d c else 0)
            + 96 * (Mat.id : Mat 8 8 Rat) b c * (if a = d then Y d c else 0)) := by
      intro d
      rw [mom4_amb, mom4Amb_cast, ← qite_mul c d (Y d c), ← qite_mul b d (Y d c),
        ← qite_mul a d (Y d c)]
      grind
    rw [Vec.sum_congr hd,
      qvsum_add (fun d : Fin 8 => 96 * (Mat.id : Mat 8 8 Rat) a b * (if c = d then Y d c else 0))
        (fun d : Fin 8 => 96 * (Mat.id : Mat 8 8 Rat) a c * (if b = d then Y d c else 0)
          + 96 * (Mat.id : Mat 8 8 Rat) b c * (if a = d then Y d c else 0)),
      qvsum_add (fun d : Fin 8 => 96 * (Mat.id : Mat 8 8 Rat) a c * (if b = d then Y d c else 0))
        (fun d : Fin 8 => 96 * (Mat.id : Mat 8 8 Rat) b c * (if a = d then Y d c else 0)),
      ← qmul_vsum (96 * (Mat.id : Mat 8 8 Rat) a b) (fun d : Fin 8 => if c = d then Y d c else 0),
      ← qmul_vsum (96 * (Mat.id : Mat 8 8 Rat) a c) (fun d : Fin 8 => if b = d then Y d c else 0),
      ← qmul_vsum (96 * (Mat.id : Mat 8 8 Rat) b c) (fun d : Fin 8 => if a = d then Y d c else 0),
      qvsum_ite_eq c (fun d : Fin 8 => Y d c), qvsum_ite_eq b (fun d : Fin 8 => Y d c),
      qvsum_ite_eq a (fun d : Fin 8 => Y d c)]
  rw [Vec.sum_congr hinner,
    qvsum_add (fun c : Fin 8 => 96 * (Mat.id : Mat 8 8 Rat) a b * Y c c)
      (fun c : Fin 8 => 96 * (Mat.id : Mat 8 8 Rat) a c * Y b c
        + 96 * (Mat.id : Mat 8 8 Rat) b c * Y a c),
    qvsum_add (fun c : Fin 8 => 96 * (Mat.id : Mat 8 8 Rat) a c * Y b c)
      (fun c : Fin 8 => 96 * (Mat.id : Mat 8 8 Rat) b c * Y a c),
    ← qmul_vsum (96 * (Mat.id : Mat 8 8 Rat) a b) (fun c : Fin 8 => Y c c)]
  have h2 : Vec.sum (fun c : Fin 8 => 96 * (Mat.id : Mat 8 8 Rat) a c * Y b c)
      = 96 * Y b a := by
    have hc : ∀ c : Fin 8, 96 * (Mat.id : Mat 8 8 Rat) a c * Y b c
        = 96 * (if a = c then Y b c else 0) := by
      intro c
      rw [← qite_mul a c (Y b c)]
      grind
    rw [Vec.sum_congr hc, ← qmul_vsum 96 (fun c : Fin 8 => if a = c then Y b c else 0),
      qvsum_ite_eq a (fun c : Fin 8 => Y b c)]
  have h3 : Vec.sum (fun c : Fin 8 => 96 * (Mat.id : Mat 8 8 Rat) b c * Y a c)
      = 96 * Y a b := by
    have hc : ∀ c : Fin 8, 96 * (Mat.id : Mat 8 8 Rat) b c * Y a c
        = 96 * (if b = c then Y a c else 0) := by
      intro c
      rw [← qite_mul b c (Y a c)]
      grind
    rw [Vec.sum_congr hc, ← qmul_vsum 96 (fun c : Fin 8 => if b = c then Y a c else 0),
      qvsum_ite_eq b (fun c : Fin 8 => Y a c)]
  rw [h2, h3]
  rfl

/-- `S34`. `S_amb = 3.Id + (3/2) tr(.) I` exactly: the ambient roots resolve
the identity up to trace. `S_amb` is the frame operator `D61` of all `120`
classes, and `Id` is the identity of `Sym^2(Q^O)`, so the statement is read at
a symmetric `Y`; on the antisymmetric part `S_amb` is zero and the identity
fails, which is why `Sym^2` and not `M_8(Q)` is the space section 17.6 puts the
operator on.

The proof is one exact identity of integers, not an estimate: the fourth moment
tensor of the `120` classes is `96` times the symmetriser (`mom4_amb`), which is
the spherical `4`-design property of the root system in the `2x` scaling, and
`(1/64) . 96 = 3/2` is where the document's `3/2` comes from. -/
public theorem S34 (Y : Mat 8 8 Rat) (hY : ∀ a b : Fin 8, Y a b = Y b a) (a b : Fin 8) :
    D61 fullK Y a b
      = 3 * Y a b + ((3 : Rat) / 2) * traceQ Y * (Mat.id : Mat 8 8 Rat) a b := by
  refine rat_cancel64 ?_
  rw [D61_expand, S34_sum, hY b a]
  have h1 : (64 : Rat) * ((3 : Rat) / 2) = 96 := by decide +kernel
  grind

/-- `S35`. `S_res = S_amb - S_atlas` as operators, exactly. The first clause is
the additivity `X |-> S_X` has by construction -- the sum defining `D61` is
supported on `X`, so a class set and its residue split it -- and the second is
the document's form of it. Stated for an arbitrary class set, since the residue
of `S22` is the only thing used. -/
public theorem S35 (W : Bitset) (Y : Mat 8 8 Rat) :
    (∀ a b : Fin 8, D61 fullK Y a b = D61 W Y a b + D61 (residue W) Y a b)
      ∧ (∀ a b : Fin 8, D61 (residue W) Y a b = D61 fullK Y a b - D61 W Y a b) := by
  have hadd : ∀ a b : Fin 8, D61 fullK Y a b = D61 W Y a b + D61 (residue W) Y a b := by
    intro a b
    have hterm : ∀ k, k < 120 →
        (if k ∈ fullK then traceQ (Mat.mul (projQ (kOf k)) Y) * projQ (kOf k) a b else 0)
          = (if k ∈ W then traceQ (Mat.mul (projQ (kOf k)) Y) * projQ (kOf k) a b else 0)
            + (if k ∈ residue W then
                traceQ (Mat.mul (projQ (kOf k)) Y) * projQ (kOf k) a b else 0) := by
      intro k hk
      have hf : k ∈ fullK := (mem_fullK k).mpr hk
      by_cases h : k ∈ W
      · rw [if_pos hf, if_pos h, if_neg (fun hh => ((mem_residue (⟨k, hk⟩ : K)).mp hh) h)]
        exact (Rat.add_zero _).symm
      · rw [if_pos hf, if_neg h, if_pos ((mem_residue (⟨k, hk⟩ : K)).mpr h)]
        exact (Rat.zero_add _).symm
    show qsumN (fun u => if u ∈ fullK then
        traceQ (Mat.mul (projQ (kOf u)) Y) * projQ (kOf u) a b else 0) 120
      = qsumN (fun u => if u ∈ W then
          traceQ (Mat.mul (projQ (kOf u)) Y) * projQ (kOf u) a b else 0) 120
        + qsumN (fun u => if u ∈ residue W then
          traceQ (Mat.mul (projQ (kOf u)) Y) * projQ (kOf u) a b else 0) 120
    rw [← qsumN_addFun
      (fun u => if u ∈ W then traceQ (Mat.mul (projQ (kOf u)) Y) * projQ (kOf u) a b else 0)
      (fun u => if u ∈ residue W then
        traceQ (Mat.mul (projQ (kOf u)) Y) * projQ (kOf u) a b else 0) 120]
    exact qsumN_congr _ _ 120 hterm
  refine ⟨hadd, fun a b => ?_⟩
  have h := hadd a b
  grind

/-- `S_X(I) = (|X|/O) I` at the AtlasInstance: the `2`-design property of `S17`
read at the one point `I` of `Sym^2`. -/
public theorem D61_atlSet_id (a b : Fin 8) :
    D61 atlSet (Mat.id : Mat 8 8 Rat) a b = ((48 : Rat) / 8) * (Mat.id : Mat 8 8 Rat) a b := by
  have h : frameSum atlSet a b = if a = b then 48 else 0 :=
    S17.2.1 ⟨2, by omega⟩ (by decide) a b
  rw [frameOp_id atlSet a b, projSum_eq]
  show (8 : Rat)⁻¹ * ((frameSum atlSet a b : Int) : Rat)
    = ((48 : Rat) / 8) * (if a = b then (1 : Rat) else 0)
  rw [h]
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab]; decide +kernel
  · rw [if_neg hab, if_neg hab]; decide +kernel

/-- The same at the residue: `S_res(I) = (72/O) I`. -/
public theorem D61_residue_id (a b : Fin 8) :
    D61 (residue atlSet) (Mat.id : Mat 8 8 Rat) a b
      = ((72 : Rat) / 8) * (Mat.id : Mat 8 8 Rat) a b := by
  have h : frameSum (residue atlSet) a b = if a = b then 72 else 0 :=
    S17.2.1 ⟨1, by omega⟩ (by decide) a b
  rw [frameOp_id (residue atlSet) a b, projSum_eq]
  show (8 : Rat)⁻¹ * ((frameSum (residue atlSet) a b : Int) : Rat)
    = ((72 : Rat) / 8) * (if a = b then (1 : Rat) else 0)
  rw [h]
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab]; decide +kernel
  · rw [if_neg hab, if_neg hab]; decide +kernel

/-- `S36`. The residue spectrum is a corollary of the AtlasInstance spectrum,
by `S34` and `S35`. Substituting `S34` into `S35` at `W = atlSet` gives
`S_res = 3.Id - S_atlas` on the traceless part of `Sym^2`, so a vector is an
eigenvector of `S_atlas` at `mu` exactly when it is one of `S_res` at `3 - mu`:
the whole traceless spectrum transports along `lambda |-> 3 - lambda`, with the
eigenvectors themselves, hence with the multiplicities. The remaining direction
of `Sym^2` is the line of `I`, which is not traceless, and there the two
operators are the `2`-design scalars `48/O` and `72/O` of `S17`. -/
public theorem S36 :
    (∀ Y : Mat 8 8 Rat, (∀ a b : Fin 8, Y a b = Y b a) → traceQ Y = 0 → ∀ a b : Fin 8,
        D61 (residue atlSet) Y a b = 3 * Y a b - D61 atlSet Y a b)
      ∧ (∀ Y : Mat 8 8 Rat, (∀ a b : Fin 8, Y a b = Y b a) → traceQ Y = 0 → ∀ mu : Rat,
          (∀ a b : Fin 8, D61 atlSet Y a b = mu * Y a b)
            ↔ (∀ a b : Fin 8, D61 (residue atlSet) Y a b = (3 - mu) * Y a b))
      ∧ (∀ a b : Fin 8, D61 atlSet (Mat.id : Mat 8 8 Rat) a b
          = ((48 : Rat) / 8) * (Mat.id : Mat 8 8 Rat) a b)
      ∧ (∀ a b : Fin 8, D61 (residue atlSet) (Mat.id : Mat 8 8 Rat) a b
          = ((72 : Rat) / 8) * (Mat.id : Mat 8 8 Rat) a b) := by
  have hsplit : ∀ Y : Mat 8 8 Rat, (∀ a b : Fin 8, Y a b = Y b a) → traceQ Y = 0 →
      ∀ a b : Fin 8, D61 (residue atlSet) Y a b = 3 * Y a b - D61 atlSet Y a b := by
    intro Y hY htr a b
    have h1 := (S35 atlSet Y).2 a b
    have h2 := S34 Y hY a b
    rw [htr] at h2
    have h3 : D61 fullK Y a b = 3 * Y a b := by rw [h2]; grind
    rw [h1, h3]
  refine ⟨hsplit, fun Y hY htr mu => ⟨fun h a b => ?_, fun h a b => ?_⟩,
    D61_atlSet_id, D61_residue_id⟩
  · rw [hsplit Y hY htr a b, h a b]; grind
  · have h1 := hsplit Y hY htr a b
    have h2 := h a b
    grind

/-! ### `S33`: `A_X = 4(M_X - I)`, and `spec(M_X) = spec(S_X)` off zero -/

/-- `c` is an eigenvector of `M_X` at `mu`. -/
@[expose] public def EigGram {m : Nat} (x : Fin m → K) (mu : Rat) (c : Vec m Rat) : Prop :=
  ∀ i : Fin m, Vec.sum (fun j : Fin m => projGramQ x i j * c j) = mu * c i

/-- `Y` is an eigenvector of `S_X` at `mu`. -/
@[expose] public def EigFrame {m : Nat} (x : Fin m → K) (mu : Rat) (Y : Mat 8 8 Rat) : Prop :=
  ∀ a b : Fin 8, frameOpL x Y a b = mu * Y a b

/-- `c` is an eigenvector of `A_X` at `lam`. -/
@[expose] public def EigAdj {m : Nat} (x : Fin m → K) (lam : Rat) (c : Vec m Rat) : Prop :=
  ∀ i : Fin m,
    Vec.sum (fun j : Fin m => (((A (x i) (x j) : Nat) : Int) : Rat) * c j) = lam * c i

/-- The trace form against a projection is linear in the second argument, in
the shape `M_X = W_X^* W_X` needs it. -/
public theorem traceQ_mul_comb {m : Nat} (P : Mat 8 8 Rat) (x : Fin m → K) (c : Vec m Rat) :
    traceQ (Mat.mul P (projComb x c))
      = Vec.sum (fun j : Fin m => c j * traceQ (Mat.mul P (projQ (x j)))) := by
  rw [traceQ_mul_expand]
  have hpq : ∀ p q : Fin 8, P p q * projComb x c q p
      = Vec.sum (fun j : Fin m => c j * (P p q * projQ (x j) q p)) := by
    intro p q
    show P p q * Vec.sum (fun j : Fin m => c j * projQ (x j) q p) = _
    rw [qmul_vsum]
    exact Vec.sum_congr (fun j => by grind)
  rw [Vec.sum_congr (fun p => Vec.sum_congr (fun q => hpq p q)),
    ← qexch2 (fun (j : Fin m) (p : Fin 8) (q : Fin 8) => c j * (P p q * projQ (x j) q p))]
  refine Vec.sum_congr (fun j => ?_)
  rw [traceQ_mul_expand, qmul_vsum]
  refine Vec.sum_congr (fun p => ?_)
  rw [qmul_vsum]

/-- `M_X = W_X^* W_X`, on the nose. -/
public theorem projCoef_projComb {m : Nat} (x : Fin m → K) (c : Vec m Rat) (i : Fin m) :
    projCoef x (projComb x c) i = Vec.sum (fun j : Fin m => projGramQ x i j * c j) := by
  show traceQ (Mat.mul (projQ (x i)) (projComb x c)) = _
  rw [traceQ_mul_comb]
  exact Vec.sum_congr (fun j => Rat.mul_comm _ _)

public theorem projComb_smul {m : Nat} (x : Fin m → K) (r : Rat) (c : Vec m Rat) (a b : Fin 8) :
    projComb x (fun i => r * c i) a b = r * projComb x c a b := by
  show Vec.sum (fun i : Fin m => (r * c i) * projQ (x i) a b)
    = r * Vec.sum (fun i : Fin m => c i * projQ (x i) a b)
  rw [qmul_vsum]
  exact Vec.sum_congr (fun i => Rat.mul_assoc r (c i) (projQ (x i) a b))

public theorem projCoef_smul {m : Nat} (x : Fin m → K) (r : Rat) (Y : Mat 8 8 Rat) (i : Fin m) :
    projCoef x (fun p q => r * Y p q) i = r * projCoef x Y i := by
  show traceQ (Mat.mul (projQ (x i)) (fun p q => r * Y p q))
    = r * traceQ (Mat.mul (projQ (x i)) Y)
  rw [traceQ_mul_expand, traceQ_mul_expand, qmul_vsum]
  refine Vec.sum_congr (fun p => ?_)
  rw [qmul_vsum]
  exact Vec.sum_congr (fun q => by grind)

public theorem projComb_zero {m : Nat} (x : Fin m → K) (c : Vec m Rat)
    (h : ∀ i, c i = 0) (a b : Fin 8) : projComb x c a b = 0 := by
  show Vec.sum (fun i : Fin m => c i * projQ (x i) a b) = 0
  have hz : ∀ i : Fin m, c i * projQ (x i) a b = (0 : Rat) := by
    intro i; rw [h i]; exact Rat.zero_mul _
  rw [Vec.sum_congr hz]
  exact qvsum_zero

/-- `A_X = 4(M_X - I)`, the first half of `S33`, entrywise. This is
`four_trace_proj` divided by `4` and the diagonal of `ProjGram` subtracted;
injectivity of the listing is what turns `x i = x j` into `i = j`. -/
public theorem projGramQ_eq {m : Nat} (x : Fin m → K)
    (hinj : ∀ i j : Fin m, x i = x j → i = j) (i j : Fin m) :
    (((A (x i) (x j) : Nat) : Int) : Rat)
      = 4 * (projGramQ x i j - (Mat.id : Mat m m Rat) i j) := by
  have h := four_trace_proj (x i) (x j)
  have hij : (if x i = x j then (1 : Int) else 0) = (Mat.id : Mat m m Int) i j := by
    show _ = (if i = j then (1 : Int) else 0)
    by_cases hh : i = j
    · rw [if_pos hh, if_pos (congrArg x hh)]
    · rw [if_neg hh, if_neg (fun he => hh (hinj i j he))]
  have hp : ((pgram (x i) (x j) : Int) : Rat)
      = 4 * (Mat.id : Mat m m Rat) i j + (((A (x i) (x j) : Nat) : Int) : Rat) := by
    show ((4 * (if x i = x j then (1 : Int) else 0)
      + ((A (x i) (x j) : Nat) : Int) : Int) : Rat) = _
    rw [hij, Rat.intCast_add, Rat.intCast_mul, intCast_matId]
    rfl
  rw [hp] at h
  show _ = 4 * (traceQ (Mat.mul (projQ (x i)) (projQ (x j))) - (Mat.id : Mat m m Rat) i j)
  grind

/-- `M_X = I + A_X/4` applied to a coefficient vector. -/
public theorem gram_split {m : Nat} (x : Fin m → K)
    (hinj : ∀ i j : Fin m, x i = x j → i = j) (c : Vec m Rat) (i : Fin m) :
    Vec.sum (fun j : Fin m => projGramQ x i j * c j)
      = c i + (4 : Rat)⁻¹
        * Vec.sum (fun j : Fin m => (((A (x i) (x j) : Nat) : Int) : Rat) * c j) := by
  have hterm : ∀ j : Fin m, projGramQ x i j * c j
      = (Mat.id : Mat m m Rat) i j * c j
        + (4 : Rat)⁻¹ * ((((A (x i) (x j) : Nat) : Int) : Rat) * c j) := by
    intro j
    have h := projGramQ_eq x hinj i j
    have hg : projGramQ x i j
        = (Mat.id : Mat m m Rat) i j + (4 : Rat)⁻¹ * (((A (x i) (x j) : Nat) : Int) : Rat) := by
      have h4 := q4_cancel' (projGramQ x i j - (Mat.id : Mat m m Rat) i j)
      rw [← h] at h4
      grind
    rw [hg]
    grind
  rw [Vec.sum_congr hterm,
    qvsum_add (fun j : Fin m => (Mat.id : Mat m m Rat) i j * c j)
      (fun j : Fin m => (4 : Rat)⁻¹ * ((((A (x i) (x j) : Nat) : Int) : Rat) * c j)),
    ← qmul_vsum (4 : Rat)⁻¹
      (fun j : Fin m => (((A (x i) (x j) : Nat) : Int) : Rat) * c j),
    Vec.sum_congr (fun j : Fin m => qite_mul i j (c j)), qvsum_ite_eq i c]

/-- The eigenvector-level half of the document's `S37`: an eigenvector of
`M_X` at `mu` is an eigenvector of `A_X` at `4(mu - 1)` and back, so
`spec(A_X) = 4(spec(M_X) - 1)` with the eigenspaces themselves identified.

The full `S37` below combines this equivalence with the exact multiplicity and
rank-nullity ledger; this theorem keeps the reusable eigenvector step separate. -/
public theorem frameOp_eigen_shift {m : Nat} (x : Fin m → K)
    (hinj : ∀ i j : Fin m, x i = x j → i = j) (mu : Rat) (c : Vec m Rat) :
    EigGram x mu c ↔ EigAdj x (4 * (mu - 1)) c := by
  constructor
  · intro h i
    have hs := gram_split x hinj c i
    rw [h i] at hs
    have h4 := q4_cancel
      (Vec.sum (fun j : Fin m => (((A (x i) (x j) : Nat) : Int) : Rat) * c j))
    grind
  · intro h i
    rw [gram_split x hinj c i, h i, ← Rat.mul_assoc, ← Rat.mul_assoc,
      Rat.inv_mul_cancel 4 (by decide), Rat.one_mul]
    grind

/-- `S33`. `A_X = 4(M_X - I)` with `M_X = [tr(P_i P_j)]`, and the nonzero
spectrum of `M_X` is the same as that of `S_X`.

The first clause is entrywise and exact. The second is exhibited rather than
asserted: for `mu != 0` the synthesis map `c |-> W_X c` and the scaled analysis
map `Y |-> mu^-1 W_X^* Y` are mutually inverse between the eigenspace of `M_X`
at `mu` and the eigenspace of `S_X` at `mu`. Both are linear, so this identifies
the eigenspaces and not merely the eigenvalue sets, which is the strongest form
"the nonzero spectra agree" can take in a library with no dimension. It rests
on nothing but `M_X = W_X^* W_X` and `S_X = W_X W_X^*`, which are the two
factorisations `projCoef_projComb` and `frameOpL_eq` prove outright.

Stated for an injective listing `x` of `X`, the presentation `D55`, `S13` and
`S14` already use; `D61_atl_eq` reads it back onto the bitset form of `D61` at
the AtlasInstance. -/
public theorem S33 {m : Nat} (x : Fin m → K) (hinj : ∀ i j : Fin m, x i = x j → i = j) :
    (∀ i j : Fin m, (((A (x i) (x j) : Nat) : Int) : Rat)
        = 4 * (projGramQ x i j - (Mat.id : Mat m m Rat) i j))
      ∧ (∀ mu : Rat, mu ≠ 0 →
          (∀ c : Vec m Rat, EigGram x mu c →
              EigFrame x mu (projComb x c)
                ∧ (∀ i : Fin m, mu⁻¹ * projCoef x (projComb x c) i = c i))
            ∧ (∀ Y : Mat 8 8 Rat, EigFrame x mu Y →
              EigGram x mu (fun i => mu⁻¹ * projCoef x Y i)
                ∧ (∀ a b : Fin 8,
                    projComb x (fun i => mu⁻¹ * projCoef x Y i) a b = Y a b))) := by
  refine ⟨projGramQ_eq x hinj, fun mu hmu => ⟨fun c hc => ⟨?_, ?_⟩, fun Y hY => ⟨?_, ?_⟩⟩⟩
  · intro a b
    have hco : projCoef x (projComb x c) = fun i => mu * c i :=
      funext (fun i => by rw [projCoef_projComb x c i]; exact hc i)
    show projComb x (projCoef x (projComb x c)) a b = mu * projComb x c a b
    rw [hco, projComb_smul]
  · intro i
    rw [projCoef_projComb x c i, hc i, ← Rat.mul_assoc, Rat.inv_mul_cancel mu hmu, Rat.one_mul]
  · have hcomb : projComb x (projCoef x Y) = fun a b => mu * Y a b :=
      funext (fun a => funext (fun b => hY a b))
    have hMd : ∀ i : Fin m, Vec.sum (fun j : Fin m => projGramQ x i j * projCoef x Y j)
        = mu * projCoef x Y i := by
      intro i
      rw [← projCoef_projComb x (projCoef x Y) i, hcomb]
      exact projCoef_smul x mu Y i
    intro i
    have hstep : Vec.sum (fun j : Fin m => projGramQ x i j * (mu⁻¹ * projCoef x Y j))
        = mu⁻¹ * Vec.sum (fun j : Fin m => projGramQ x i j * projCoef x Y j) := by
      rw [qmul_vsum]
      exact Vec.sum_congr (fun j => by grind)
    show Vec.sum (fun j : Fin m => projGramQ x i j * (mu⁻¹ * projCoef x Y j))
      = mu * (mu⁻¹ * projCoef x Y i)
    rw [hstep, hMd i]
    grind
  · intro a b
    rw [projComb_smul x mu⁻¹ (projCoef x Y) a b,
      show projComb x (projCoef x Y) a b = mu * Y a b from hY a b,
      ← Rat.mul_assoc, Rat.inv_mul_cancel mu hmu, Rat.one_mul]

/-! ### The top of `spec(S_X)`

`apply_e_of_scalar` is `apply_e_of_eig` with the eigenvalue left free instead of
taken from the certified list; it is the step that turns a `SpecSys` into a
statement about *every* rational scalar, and hence into the bound the
top-eigenvalue theorem needs. -/

/-- A projection of a verified spectral system kills every eigenvector whose
scalar is not the projection's own eigenvalue -- the scalar being an arbitrary
rational, not one of the certified list. -/
public theorem apply_e_of_scalar {nE n : Nat} (S : SpecSys nE n) {s : Fin nE} {mu : Rat}
    (hmu : mu ≠ ((S.lam s : Int) : Rat)) (y : Vec n Rat)
    (hy : ∀ i, Mat.apply S.Aq y i = mu * y i) (i : Fin n) :
    Mat.apply (S.e s) y i = 0 := by
  have hcomm : Mat.apply (S.e s) (Mat.apply S.Aq y) i
      = Mat.apply S.Aq (Mat.apply (S.e s) y) i := by
    rw [← congrFun (Mat.apply_mul (S.e s) S.Aq y) i, S.e_comm s,
      congrFun (Mat.apply_mul S.Aq (S.e s) y) i]
  have hleft : Mat.apply (S.e s) (Mat.apply S.Aq y) i = mu * Mat.apply (S.e s) y i := by
    have hfun : Mat.apply S.Aq y = fun j => mu * y j := funext hy
    rw [hfun, apply_qsmul (S.e s) mu y i]
  have hright : Mat.apply S.Aq (Mat.apply (S.e s) y) i
      = ((S.lam s : Int) : Rat) * Mat.apply (S.e s) y i := S.apply_e_eig s y i
  have heq : mu * Mat.apply (S.e s) y i
      = ((S.lam s : Int) : Rat) * Mat.apply (S.e s) y i := by
    rw [← hleft, ← hright, hcomm]
  have hz : (mu - ((S.lam s : Int) : Rat)) * Mat.apply (S.e s) y i = 0 := by grind
  rcases Rat.mul_eq_zero.mp hz with h | h
  · exact absurd h (fun hh => hmu (by grind))
  · exact h

/-- Off the certified spectrum there is no eigenvector: the projections sum to
the identity, and each of them kills the vector. -/
public theorem eig_scalar_mem {nE n : Nat} (S : SpecSys nE n) (mu : Rat) (y : Vec n Rat)
    (hy : ∀ i, Mat.apply S.Aq y i = mu * y i)
    (hout : ∀ s : Fin nE, mu ≠ ((S.lam s : Int) : Rat)) (i : Fin n) : y i = 0 := by
  have h := S.apply_sum_e y i
  rw [Vec.sum_congr (fun s : Fin nE => apply_e_of_scalar S (hout s) y hy i)] at h
  rw [← h]
  exact qvsum_zero

public theorem atlClass_inj (i j : Fin 48) (h : atlClass i = atlClass j) : i = j := xClass_inj h

/-- `A_X` on the AtlasInstance listing is the matrix `xSpec` carries. -/
public theorem eigAdj_apply (lam : Rat) (c : Vec 48 Rat) (h : EigAdj atlClass lam c)
    (i : Fin 48) : Mat.apply xSpec.Aq c i = lam * c i := by
  have hA : ∀ j : Fin 48,
      xSpec.Aq i j = (((A (atlClass i) (atlClass j) : Nat) : Int) : Rat) := by
    intro j
    have h0 : xSpec.Aq i j = ((atlMat i j : Int) : Rat) := rfl
    rw [h0, atlMat_adj i j]
  show Vec.sum (fun j : Fin 48 => xSpec.Aq i j * c j) = lam * c i
  rw [Vec.sum_congr (fun j : Fin 48 => congrArg (fun t : Rat => t * c j) (hA j))]
  exact h i

/-- Within `spec(S_X)` the top eigenvalue is `|X|/O`, forced by the
`2`-design property. At the AtlasInstance `|X|/O = 48/8 = 6`.

The first two clauses say `48/8` is attained, the third that nothing exceeds
it. Attainment is exactly the `2`-design condition `D57` of `S17` read at the
one point `I` of `Sym^2`, through `frameOp_id`:
`S_X(I) = sum_{i in X} P_i = (|X|/O) I`, and `I` is not the zero matrix.
That nothing exceeds it is the certified spectrum: a nonzero eigenvector of
`S_X` at `mu != 0` produces, by `S33`, an eigenvector of `M_X` at `mu`, hence by
`frameOp_eigen_shift` one of `A_X` at `4(mu - 1)`; `eig_scalar_mem` at `xSpec`
then forces `4(mu - 1)` into the certified list `{20, 8, 4, 0, -4}` of `S32`,
so `mu` is one of `6, 3, 2, 1, 0`, all at most `48/8`. The zero eigenvalue is
below the bound outright.

`D61_atl_eq` is what lets the argument, which runs on the listing `atlClass`,
be stated about the `D61` of the bitset `atlSet`.

This is the AtlasInstance half of `S38`. The residue half is proved below by
transport through `S36`; the labelled theorem then joins both bounds to the
two codimensions from `S15`. -/
public theorem topEigenvalue_atlas :
    (∀ a b : Fin 8, D61 atlSet (Mat.id : Mat 8 8 Rat) a b
        = ((48 : Rat) / 8) * (Mat.id : Mat 8 8 Rat) a b)
      ∧ (∃ p q : Fin 8, (Mat.id : Mat 8 8 Rat) p q ≠ 0)
      ∧ (∀ (mu : Rat) (Y : Mat 8 8 Rat), (∃ p q : Fin 8, Y p q ≠ 0) →
          (∀ a b : Fin 8, D61 atlSet Y a b = mu * Y a b) → mu ≤ (48 : Rat) / 8) := by
  have hgoal : ∀ v : Nat, v < 5 →
      (4 : Rat)⁻¹ * (((atlLam v : Int) : Rat) + 4) ≤ (48 : Rat) / 8 := by
    intro v hv
    match v, hv with
    | 0, _ => decide +kernel
    | 1, _ => decide +kernel
    | 2, _ => decide +kernel
    | 3, _ => decide +kernel
    | 4, _ => decide +kernel
    | (p + 5), h => exact absurd h (by omega)
  refine ⟨D61_atlSet_id, ⟨0, 0, by decide +kernel⟩, fun mu Y hY0 hEig => ?_⟩
  by_cases hmu : mu = 0
  · rw [hmu]; decide +kernel
  · have hEigF : EigFrame atlClass mu Y := by
      intro a b
      rw [← D61_atl_eq Y a b]
      exact hEig a b
    obtain ⟨hgram, hback⟩ := ((S33 atlClass atlClass_inj).2 mu hmu).2 Y hEigF
    have hcne : ¬ (∀ i : Fin 48, mu⁻¹ * projCoef atlClass Y i = 0) := by
      intro hz
      obtain ⟨p, q, hpq⟩ := hY0
      refine hpq ?_
      rw [← hback p q]
      exact projComb_zero atlClass (fun i => mu⁻¹ * projCoef atlClass Y i) hz p q
    have hadj : EigAdj atlClass (4 * (mu - 1)) (fun i => mu⁻¹ * projCoef atlClass Y i) :=
      (frameOp_eigen_shift atlClass atlClass_inj mu _).mp hgram
    have happ : ∀ i : Fin 48,
        Mat.apply xSpec.Aq (fun i => mu⁻¹ * projCoef atlClass Y i) i
          = (4 * (mu - 1)) * (mu⁻¹ * projCoef atlClass Y i) :=
      eigAdj_apply (4 * (mu - 1)) _ hadj
    have hex : ∃ s : Fin 5, (4 : Rat) * (mu - 1) = ((xSpec.lam s : Int) : Rat) :=
      Classical.byContradiction (fun hno =>
        hcne (fun i => eig_scalar_mem xSpec ((4 : Rat) * (mu - 1)) _ happ
          (fun s h => hno ⟨s, h⟩) i))
    obtain ⟨s, hs⟩ := hex
    have hlam : xSpec.lam s = atlLam s.val := rfl
    have hs' : (4 : Rat) * (mu - 1) = ((atlLam s.val : Int) : Rat) := by rw [hs, hlam]
    have hmu4 : (4 : Rat) * mu = ((atlLam s.val : Int) : Rat) + 4 := by grind
    have hmuv : mu = (4 : Rat)⁻¹ * (((atlLam s.val : Int) : Rat) + 4) := by
      have hq := q4_cancel' mu
      rw [hmu4] at hq
      exact hq.symm
    rw [hmuv]
    exact hgoal s.val s.isLt

/-! ### The residue bound and the two remaining spectral labels

The residue does not need a second spectral-projector table.  The frame
operator is self-adjoint for the trace form, so a nonzero eigenvector is
symmetric and, away from the design scalar `9`, traceless.  `S36` then carries
it to the AtlasInstance, where `xSpec` is exhaustive.  This proves the bound at
the second instance named by `S38` without sampling eigenvalues or assuming
positivity.
-/

/-- Self-adjointness at the identity: the trace of `S_X(Y)` is the trace form
of `Y` against `sum_i P_i`. -/
public theorem trace_frameOp (W : Bitset) (Y : Mat 8 8 Rat) :
    traceQ (D61 W Y) = traceQ (Mat.mul (projSum W) Y) := by
  have hleft : traceQ (D61 W Y) = Vec.sum (fun u : K =>
      if u.val ∈ W then traceQ (Mat.mul (projQ u) Y) else 0) := by
    show Vec.sum (fun a : Fin 8 => D61 W Y a a) = _
    rw [Vec.sum_congr (fun a => D61_vecsum W Y a a)]
    rw [Vec.sum_exchange (fun (a : Fin 8) (u : K) =>
      if u.val ∈ W then mul (traceQ (Mat.mul (projQ u) Y)) (projQ u a a) else zero)]
    refine Vec.sum_congr (fun u => ?_)
    by_cases hu : u.val ∈ W
    · rw [if_pos hu, Vec.sum_congr (fun a => if_pos hu), ← Vec.mul_sum]
      have htr : Vec.sum (fun a : Fin 8 => projQ u a a) = 1 := (projQ_symm_trace u).2
      rw [htr]
      exact Rat.mul_one _
    · rw [if_neg hu, Vec.sum_congr (fun a => if_neg hu)]
      exact qvsum_zero
  have hright : traceQ (Mat.mul (projSum W) Y) = Vec.sum (fun u : K =>
      if u.val ∈ W then traceQ (Mat.mul (projQ u) Y) else 0) := by
    rw [traceQ_mul_expand]
    have hp : ∀ a b : Fin 8, projSum W a b = Vec.sum (fun u : K =>
        if u.val ∈ W then projQ u a b else 0) := by
      intro a b
      show qsumN (fun u => if u ∈ W then projQ (kOf u) a b else 0) 120 = _
      rw [← qsumN_eq_vecsum]
      refine Vec.sum_congr (fun u => ?_)
      have ku : kOf u.val = u := Fin.eq_of_val_eq (Nat.mod_eq_of_lt u.isLt)
      rw [ku]
    rw [Vec.sum_congr (fun a => Vec.sum_congr (fun b =>
      congrArg (fun z : Rat => z * Y b a) (hp a b)))]
    calc
      Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 =>
          Vec.sum (fun u : K => if u.val ∈ W then projQ u a b else 0) * Y b a))
          = Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 =>
              Vec.sum (fun u : K => (if u.val ∈ W then projQ u a b else 0) * Y b a))) :=
            Vec.sum_congr (fun a => Vec.sum_congr (fun b => Vec.sum_mul _ _))
      _ = Vec.sum (fun u : K => Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 =>
          (if u.val ∈ W then projQ u a b else 0) * Y b a))) :=
            (qexch2 (fun (u : K) (a b : Fin 8) =>
              (if u.val ∈ W then projQ u a b else 0) * Y b a)).symm
      _ = Vec.sum (fun u : K =>
          if u.val ∈ W then traceQ (Mat.mul (projQ u) Y) else 0) := by
            refine Vec.sum_congr (fun u => ?_)
            by_cases hu : u.val ∈ W
            · simp only [if_pos hu]
              change Vec.sum (fun a : Fin 8 => Vec.sum (fun b : Fin 8 =>
                projQ u a b * Y b a)) = traceQ (Mat.mul (projQ u) Y)
              exact traceQ_mul_expand (projQ u) Y |>.symm
            · simp only [if_neg hu]
              change Vec.sum (fun _a : Fin 8 => Vec.sum (fun _b : Fin 8 =>
                (0 : Rat) * Y _b _a)) = 0
              have hz : ∀ a b : Fin 8, (0 : Rat) * Y b a = 0 := fun a b => Rat.zero_mul _
              rw [Vec.sum_congr (fun a => Vec.sum_congr (fun b => hz a b)),
                Vec.sum_congr (fun _ : Fin 8 => qvsum_zero), qvsum_zero]
  exact hleft.trans hright.symm

public theorem trace_frameOp_design (W : Bitset) (Y : Mat 8 8 Rat) (c : Rat)
    (hdesign : ∀ a b : Fin 8, projSum W a b = c * (Mat.id : Mat 8 8 Rat) a b) :
    traceQ (D61 W Y) = c * traceQ Y := by
  rw [trace_frameOp]
  show Vec.sum (fun a : Fin 8 => Mat.mul (projSum W) Y a a) =
    c * Vec.sum (fun a : Fin 8 => Y a a)
  rw [Vec.sum_congr (fun a => ?_), qmul_vsum]
  show Vec.sum (fun b : Fin 8 => projSum W a b * Y b a) = c * Y a a
  rw [Vec.sum_congr (fun b => congrArg (fun z : Rat => z * Y b a) (hdesign a b))]
  have ht : ∀ b : Fin 8,
      (c * (Mat.id : Mat 8 8 Rat) a b) * Y b a = if a = b then c * Y b a else 0 := by
    intro b
    by_cases hab : a = b
    · rw [if_pos hab]
      show (c * (if a = b then (1 : Rat) else 0)) * Y b a = c * Y b a
      rw [if_pos hab, Rat.mul_one]
    · rw [if_neg hab]
      show (c * (if a = b then (1 : Rat) else 0)) * Y b a = 0
      rw [if_neg hab, Rat.mul_zero, Rat.zero_mul]
  rw [Vec.sum_congr ht]
  exact qvsum_ite_eq a (fun b => c * Y b a)

public theorem frameOp_symm (W : Bitset) (Y : Mat 8 8 Rat) (a b : Fin 8) :
    D61 W Y a b = D61 W Y b a := by
  show qsumN (fun u => if u ∈ W then
      traceQ (Mat.mul (projQ (kOf u)) Y) * projQ (kOf u) a b else 0) 120 = _
  refine qsumN_congr _ _ 120 (fun u _ => ?_)
  by_cases hu : u ∈ W
  · rw [if_pos hu, if_pos hu, (projQ_symm_trace (kOf u)).1 a b]
  · rw [if_neg hu, if_neg hu]

public theorem eigFrame_symm (W : Bitset) (Y : Mat 8 8 Rat) (mu : Rat) (hmu : mu ≠ 0)
    (hEig : ∀ a b : Fin 8, D61 W Y a b = mu * Y a b) (a b : Fin 8) :
    Y a b = Y b a := by
  have h : mu * Y a b = mu * Y b a := by
    rw [← hEig a b, ← hEig b a, frameOp_symm W Y a b]
  have hz : mu * (Y a b - Y b a) = 0 := by grind
  rcases Rat.mul_eq_zero.mp hz with h0 | h0
  · exact absurd h0 hmu
  · grind

public theorem eigFrame_trace_zero (W : Bitset) (Y : Mat 8 8 Rat) (mu c : Rat)
    (hmu : mu ≠ c)
    (hdesign : ∀ a b : Fin 8, projSum W a b = c * (Mat.id : Mat 8 8 Rat) a b)
    (hEig : ∀ a b : Fin 8, D61 W Y a b = mu * Y a b) : traceQ Y = 0 := by
  have h1 := trace_frameOp_design W Y c hdesign
  have h2 : traceQ (D61 W Y) = mu * traceQ Y := by
    show Vec.sum (fun a : Fin 8 => D61 W Y a a) = mu * Vec.sum (fun a : Fin 8 => Y a a)
    rw [Vec.sum_congr (fun a => hEig a a), qmul_vsum]
  rw [h2] at h1
  have hz : (mu - c) * traceQ Y = 0 := by grind
  rcases Rat.mul_eq_zero.mp hz with h0 | h0
  · exact absurd h0 (fun hh => hmu (by grind))
  · exact h0

/-- At the residue, `9 = 72/8` is attained on the identity and bounds every
rational eigenvalue.  The proof transports the traceless part through `S36`
and uses the exhaustive AtlasInstance projectors. -/
public theorem topEigenvalue_residue :
    (∀ a b : Fin 8, D61 (residue atlSet) (Mat.id : Mat 8 8 Rat) a b
        = ((72 : Rat) / 8) * (Mat.id : Mat 8 8 Rat) a b)
      ∧ (∃ p q : Fin 8, (Mat.id : Mat 8 8 Rat) p q ≠ 0)
      ∧ (∀ (mu : Rat) (Y : Mat 8 8 Rat), (∃ p q : Fin 8, Y p q ≠ 0) →
          (∀ a b : Fin 8, D61 (residue atlSet) Y a b = mu * Y a b) →
          mu ≤ (72 : Rat) / 8) := by
  refine ⟨D61_residue_id, ⟨0, 0, by decide +kernel⟩, fun mu Y hY0 hEig => ?_⟩
  have h9 : ((72 : Rat) / 8) = 9 := by decide +kernel
  rw [h9]
  by_cases hmu0 : mu = 0
  · rw [hmu0]; decide +kernel
  by_cases hmu9 : mu = 9
  · rw [hmu9]; decide +kernel
  by_cases hmu3 : mu = 3
  · rw [hmu3]; decide +kernel
  have hsym : ∀ a b : Fin 8, Y a b = Y b a := eigFrame_symm _ _ _ hmu0 hEig
  have hdesign : ∀ a b : Fin 8,
      projSum (residue atlSet) a b = 9 * (Mat.id : Mat 8 8 Rat) a b := by
    intro a b
    rw [← frameOp_id (residue atlSet) a b, D61_residue_id, h9]
  have htr : traceQ Y = 0 := eigFrame_trace_zero _ _ _ _ hmu9 hdesign hEig
  let nu : Rat := 3 - mu
  have hnu : nu ≠ 0 := by intro h; apply hmu3; dsimp [nu] at h; grind
  have hAtl : ∀ a b : Fin 8, D61 atlSet Y a b = nu * Y a b := by
    have hiff := S36.2.1 Y hsym htr nu
    apply hiff.mpr
    intro a b
    rw [hEig a b]
    dsimp [nu]
    grind
  have hEigF : EigFrame atlClass nu Y := by
    intro a b
    rw [← D61_atl_eq Y a b]
    exact hAtl a b
  let coeff : Vec 48 Rat := fun i => nu⁻¹ * projCoef atlClass Y i
  have hpair := (S33 atlClass atlClass_inj).2 nu hnu |>.2 Y hEigF
  have hgram : EigGram atlClass nu coeff := hpair.1
  have hrecon : ∀ a b : Fin 8, projComb atlClass coeff a b = Y a b := hpair.2
  let lam : Rat := 4 * (nu - 1)
  have hadj : EigAdj atlClass lam coeff :=
    frameOp_eigen_shift atlClass atlClass_inj nu coeff |>.mp hgram
  have happly : ∀ i : Fin 48, Mat.apply xSpec.Aq coeff i = lam * coeff i :=
    eigAdj_apply lam coeff hadj
  have hmem : ∃ t : Fin 5, lam = ((xSpec.lam t : Int) : Rat) := by
    apply Classical.byContradiction
    intro hn
    have hout : ∀ t : Fin 5, lam ≠ ((xSpec.lam t : Int) : Rat) := by
      intro t ht
      exact hn ⟨t, ht⟩
    have hzero : ∀ i : Fin 48, coeff i = 0 :=
      fun i => eig_scalar_mem xSpec lam coeff happly hout i
    obtain ⟨p, q, hpq⟩ := hY0
    apply hpq
    rw [← hrecon p q]
    show Vec.sum (fun i : Fin 48 => coeff i * projQ (atlClass i) p q) = 0
    rw [Vec.sum_congr (fun i => by rw [hzero i, Rat.zero_mul])]
    exact qvsum_zero
  obtain ⟨t, ht⟩ := hmem
  dsimp [lam, nu] at ht
  match t with
  | ⟨0, _⟩ => change 4 * (3 - mu - 1) = (20 : Rat) at ht; grind
  | ⟨1, _⟩ => change 4 * (3 - mu - 1) = (8 : Rat) at ht; grind
  | ⟨2, _⟩ => change 4 * (3 - mu - 1) = (4 : Rat) at ht; grind
  | ⟨3, _⟩ => change 4 * (3 - mu - 1) = (0 : Rat) at ht; grind
  | ⟨4, _⟩ => change 4 * (3 - mu - 1) = (-4 : Rat) at ht; grind
  | ⟨n + 5, hn⟩ => exact absurd hn (by omega)

/-- `S37`.  `A_X` and `S_X` have the same nonzero eigenspaces after the affine
shift `lambda = 4(mu-1)` (`S33` supplies the mutually inverse maps), and the
`-4` multiplicities give `|X| - rank(S_X)` at every scale of the tower.

The second clause is the exact five-scale rank-nullity ledger.  Its
multiplicities are uniquely pinned by the annihilating polynomials and traces
of `S32`; at the AtlasInstance the `18`-dimensional eigenspace additionally
has the split rank certificate `xHasRank`. -/
public theorem S37 :
    (∀ {m : Nat} (x : Fin m → K) (_hinj : ∀ i j : Fin m, x i = x j → i = j)
        (mu : Rat) (c : Vec m Rat),
        EigGram x mu c ↔ EigAdj x (4 * (mu - 1)) c)
      ∧ ((ambLam 2 = -4 ∧ ambMult 2 = 84 ∧ 120 - 84 = 36 ∧ 36 - 36 = 0)
        ∧ (resLam 4 = -4 ∧ resMult 4 = 38 ∧ 72 - 38 = 34 ∧ 36 - 34 = 2)
        ∧ (atlLam 4 = -4 ∧ atlMult 4 = 18 ∧ 48 - 18 = 30 ∧ 36 - 30 = 6)
        ∧ (frmLam 2 = -4 ∧ frmMult 2 = 4 ∧ 24 - 4 = 20 ∧ 36 - 20 = 16)
        ∧ (blkLam 2 = -4 ∧ blkMult 2 = 2 ∧ 12 - 2 = 10 ∧ 10 - 10 = 0)
        ∧ (8 * (8 + 1) / 2 = 36 ∧ 4 * (4 + 1) / 2 = 10))
      ∧ HasMatRank (xSpec.e 4) 18 :=
  ⟨fun x hinj mu c => frameOp_eigen_shift x hinj mu c, S15, xHasRank 4⟩

/-- `S38`.  The design scalar `|X|/8` is the top eigenvalue at both instances
named by the document, and the zero multiplicities are the two codimensions
from `S15`: `6` for the `48`-class AtlasInstance and `2` for its `72`-class
residue. -/
public theorem S38 :
    ((∀ a b : Fin 8, D61 atlSet (Mat.id : Mat 8 8 Rat) a b
        = ((48 : Rat) / 8) * (Mat.id : Mat 8 8 Rat) a b)
      ∧ (∃ p q : Fin 8, (Mat.id : Mat 8 8 Rat) p q ≠ 0)
      ∧ (∀ (mu : Rat) (Y : Mat 8 8 Rat), (∃ p q : Fin 8, Y p q ≠ 0) →
          (∀ a b : Fin 8, D61 atlSet Y a b = mu * Y a b) → mu ≤ (48 : Rat) / 8))
      ∧ ((∀ a b : Fin 8, D61 (residue atlSet) (Mat.id : Mat 8 8 Rat) a b
        = ((72 : Rat) / 8) * (Mat.id : Mat 8 8 Rat) a b)
      ∧ (∃ p q : Fin 8, (Mat.id : Mat 8 8 Rat) p q ≠ 0)
      ∧ (∀ (mu : Rat) (Y : Mat 8 8 Rat), (∃ p q : Fin 8, Y p q ≠ 0) →
          (∀ a b : Fin 8, D61 (residue atlSet) Y a b = mu * Y a b) →
          mu ≤ (72 : Rat) / 8))
      ∧ (36 - (48 - atlMult 4) = 6 ∧ 36 - (72 - resMult 4) = 2) :=
  ⟨topEigenvalue_atlas, topEigenvalue_residue, by decide⟩

end UorAtlas.Scales
