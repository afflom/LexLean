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

/-- The inner product of two distinct class representatives is `0` or `+-4`:
the values `+-8` are excluded because they force `v = +-u`. This is the one
finite check that makes orthogonality and adjacency complementary, and it is
what `D52` and `D13` are read against everywhere below. -/
public theorem dotTri :
    allLt (fun i => allLt (fun j => decide (i = j)
      || decide (dot8 (repN i) (repN j) = 0)
      || decide (dot8 (repN i) (repN j) = 4)
      || decide (dot8 (repN i) (repN j) = -4)) 120) 120 = true := by
  decide +kernel

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
which `T14`-`T19` are: a statement about *every* block quantifies over the
census `Blk`, which that module explains it does not have. `S8` is about `K`
itself and is unconditional. -/

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

/-- Pulling a scalar out of an integer sum on the left. -/
public theorem isum_mul_left {n : Nat} (c : Int) (x : Vec n Int) :
    c * Vec.sum x = Vec.sum (fun i => c * x i) := Vec.mul_sum c x

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
    ← isum_mul_left (b * b') (fun k : K => Aint u k * Aint k v),
    ← isum_mul_left (b * c') (fun k : K => Aint u k),
    isum_ite' v (fun _ : K => c * a'),
    ← isum_mul_left (c * b') (fun k : K => Aint k v),
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

end UorAtlas.Scales
