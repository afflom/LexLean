module

public import Init
public import UorAtlas.Prelude.Algebra
public import UorAtlas.Prelude.Linear
public import UorAtlas.Prelude.Bitset
public import UorAtlas.Roots
public import UorAtlas.Blocks
public import UorAtlas.Group

/-!
# The block census

`T22` to `T24` are three counts: `|Blk| = 3150`, `|Frm| = 1575`, `|Atl| = 75600`.
A count is two obligations, and only one of them is a computation. Exhibiting
`3150` blocks is a computation. Showing there are no others is not, and a list
that only ever grows by enumeration cannot discharge it.

This module is the computation, and it is arranged so that the second
obligation becomes small rather than being left open.

## Why an orthogonal quadruple, and not any four classes

A block is `12` classes of rank `4`. Any four independent classes of a block
span it, so a block is the set of classes in the span of four of its own
members -- but there are `C(120,4)` such quadruples and a span test costs a
linear solve, which is `10^9` kernel operations and out of reach.

Restricting to *orthogonal* quadruples collapses the span test to a bitset
intersection. The class representatives pair to `0`, `+-4` or `8`, and `8` only
on the diagonal. So for an orthogonal quadruple `q` and any class `v`,
Parseval reads

    v in span(q)   <->   sum_i <v,q_i>^2 = 64

and each summand is `64` (when `v` is `q_i`), `16` (when `v` is adjacent to
`q_i`) or `0`. The sum reaches `64` in exactly two ways: `v` is one of the four,
or `v` is adjacent to all four. Hence

    closure(q) = q  u  (adj(q_0) n adj(q_1) n adj(q_2) n adj(q_3))

which is three `AND`s and a test for emptiness. That is `quadClosure` below.
It is a proof about the pairing values, not an enumeration over quadruples.

## Why no deduplication pass

Each block contains exactly three orthogonal quadruples and they partition its
twelve classes, so exactly one of them contains the block's least class. A
quadruple `a < b < c < d` is that one exactly when `a` is below every class of
the intersection, which is `inter % 2^(a+1) = 0`. Filtering on it emits each
block exactly once, so the enumeration counts blocks rather than quadruples and
needs no `O(n^2)` deduplication pass -- and nothing has to be materialised in
order to be counted.

## What is proved here, and what is not

`T22` is `|Blk| = 3150`, and a cardinality is two obligations: exhibiting the
blocks, and showing there are no others.

The first is discharged below. `blkExhibit` names `3150` pairwise distinct
`D16` blocks -- the table of quadruples, each entry certified against
`block_of_quad` -- so `|Blk| >= 3150` is a theorem and not an enumeration's
say-so.

The second is discharged in part. `quad_in_table` proves that no closure
escapes the table: every orthogonal quadruple whose closure holds twelve
classes closes to an entry of it. What is left is the implication neither half
supplies, that a `D16` block *is* the closure of an orthogonal quadruple --
that its twelve classes contain four pairwise orthogonal ones. While that is
open this module carries **no** `T22`, and `T23`, `T24`, `T25`, `T25x`, `T26`,
`T26x` and `T27` -- which quantify over the completed census, over `Blk`, over
`Frm`, over all of `Atl` -- are absent for the same reason. "What completeness
still needs", at the foot of the module, records the route and the constants
that turn it on.

Two theorems below make the identity this module is built on a theorem rather
than an assertion: `mem_quadSet_iff_inSpan` proves that the closure of an
orthogonal quadruple is *exactly* the set of classes lying in its span, and
`block_of_quad` proves that a closure holding twelve classes is a `D16` block.
Both directions are Bessel's inequality over `Z`, and neither is a search.
-/

public section

namespace UorAtlas.Census

open UorAtlas.Prelude
open UorAtlas.Prelude.AddCommGroup
open UorAtlas.Prelude.CommRing
open UorAtlas.Prelude.Linear
open UorAtlas.Roots
open UorAtlas.Blocks
open UorAtlas.Group

/-! ## Masks -/

/-- The classes adjacent to `i`, as a `120`-bit mask. This is row `i` of the
packed adjacency table that `Group` already builds and `T59p0` already checks,
so the census introduces no second notion of adjacency. -/
@[expose] public def adjMask (i : Nat) : Nat := adjRow i

/-- The all-of-`K` mask. -/
@[expose] public def fullMask : Nat := Nat.sub (Nat.shiftLeft 1 120) 1

/-- The classes orthogonal to `i`: in `K`, distinct from `i`, and not adjacent
to `i`. Since the pairing values are `0`, `+-4` and `8`, and `8` occurs only at
`i` itself, "not adjacent and not equal" is exactly "pairs to zero". -/
@[expose] public def orthMask (i : Nat) : Nat :=
  Nat.land fullMask (Nat.xor fullMask (Nat.lor (adjMask i) (Nat.shiftLeft 1 i)))

/-- The set bits of `m`, in increasing order, reading from bit `i` upwards.

The mask is *halved* rather than probed. Testing the `120` bit positions of a
mask with `Nat.testBit` costs a shift and a mask of the full number at every
position, and this walk runs at every node of the enumeration -- some five
million probes, each allocating. Halving consumes the number instead: each step
is one `%` and one `/` on a value that is shrinking, and the walk stops as soon
as the mask is exhausted rather than always running to `120`.

The upward-with-append shape (`bitsOf n m ++ [n]`) is worse again: an `O(n^2)`
chain of appends, deep enough at `n = 120` to exhaust the kernel's recursion
budget before it reaches any arithmetic. -/
@[expose] public def bitsFrom : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | (f + 1), i, m =>
      if Nat.beq m 0 then []
      else if Nat.beq (Nat.mod m 2) 1 then i :: bitsFrom f (i + 1) (Nat.div m 2)
      else bitsFrom f (i + 1) (Nat.div m 2)

/-- The set bits of a `120`-bit mask, in increasing order. -/
@[expose] public def bitsOf (m : Nat) : List Nat := bitsFrom 121 0 m

/-- The mask of bits of `m` strictly above `k`. -/
@[expose] public def above (m k : Nat) : Nat :=
  Nat.land m (Nat.xor fullMask (Nat.sub (Nat.shiftLeft 1 (k + 1)) 1))

/-! ## The closure of an orthogonal quadruple -/

/-- The common adjacency of a quadruple: the classes adjacent to all four. -/
@[expose] public def commonAdj (a b c d : Nat) : Nat :=
  Nat.land (Nat.land (adjMask a) (adjMask b)) (Nat.land (adjMask c) (adjMask d))

/-- `closure(q)`: the quadruple together with its common adjacency. By the
Parseval reading above this is exactly the set of classes in `span(q)`. -/
@[expose] public def quadClosure (a b c d : Nat) : Nat :=
  Nat.lor (commonAdj a b c d)
    (Nat.lor (Nat.lor (Nat.shiftLeft 1 a) (Nat.shiftLeft 1 b))
      (Nat.lor (Nat.shiftLeft 1 c) (Nat.shiftLeft 1 d)))

/-- `a` is below every class of the quadruple's common adjacency, so `q` is the
one quadruple of its block that contains the block's least class. -/
@[expose] public def isLeastQuad (a : Nat) (inter : Nat) : Bool :=
  Nat.beq (Nat.mod inter (Nat.shiftLeft 1 (a + 1))) 0

/-! ## The enumeration

Four nested walks over masks, each level intersecting the orthogonality masks
of the levels above it, so only orthogonal quadruples are ever reached. The
counts are `120` first classes, `3780` orthogonal pairs, `40950` orthogonal
triples and `122850` orthogonal quadruples.

The masks are *threaded* rather than recomputed. `adjMask i` extracts row `i`
out of `adjPack`, which is a `14400`-bit number, so every call shifts and
allocates. Writing the walk so that each level receives the intersection its
parent already built costs one extraction per node instead of four per leaf. -/

/-- Innermost walk: `d` over the candidates, against the triple mask its
parents already intersected. -/
@[expose] public def countD (a abc : Nat) : List Nat → Nat
  | [] => 0
  | (d :: t) =>
      (let inter := Nat.land abc (adjMask d)
       if Nat.beq inter 0 then 0 else if isLeastQuad a inter then 1 else 0)
      + countD a abc t

/-- Third walk: `c`, building the triple masks handed to `countD`. -/
@[expose] public def countC (a oab ab : Nat) : List Nat → Nat
  | [] => 0
  | (c :: t) =>
      countD a (Nat.land ab (adjMask c)) (bitsOf (above (Nat.land oab (orthMask c)) c))
      + countC a oab ab t

/-- Second walk: `b`. -/
@[expose] public def countB (a oa aa : Nat) : List Nat → Nat
  | [] => 0
  | (b :: t) =>
      countC a (Nat.land oa (orthMask b)) (Nat.land aa (adjMask b))
        (bitsOf (above (Nat.land oa (orthMask b)) b))
      + countB a oa aa t

/-- The number of blocks whose least class is `a`. -/
@[expose] public def blkCountFrom (a : Nat) : Nat :=
  countB a (orthMask a) (adjMask a) (bitsOf (above (orthMask a) a))

/-- Blocks whose least class is below `n`. -/
@[expose] public def blkCountUpTo : Nat → Nat
  | 0 => 0
  | (n + 1) => blkCountUpTo n + blkCountFrom n

/-- Blocks whose least class lies in `[lo, lo + len)`.

The census is checked in windows rather than in one `decide`. The kernel
releases memory between declarations but not inside one, and the whole
enumeration in a single declaration passed `16 GB` and was still climbing; the
same work split into windows peaks at a fraction of that. The per-class work is
bounded by `4095` quadruples, so a window of a few classes is a fixed, small
cost. -/
@[expose] public def blkCountRange (lo : Nat) : Nat → Nat
  | 0 => 0
  | (n + 1) => blkCountRange lo n + blkCountFrom (lo + n)

/-- Windows compose: counting `[0, lo)` and then `[lo, lo + len)` counts
`[0, lo + len)`. Symbolic, so it costs nothing to check. -/
public theorem blkCountUpTo_add (lo : Nat) : ∀ len : Nat,
    blkCountUpTo (lo + len) = blkCountUpTo lo + blkCountRange lo len := by
  intro len
  induction len with
  | zero => rfl
  | succ n ih =>
    show blkCountUpTo (lo + n) + blkCountFrom (lo + n)
      = blkCountUpTo lo + (blkCountRange lo n + blkCountFrom (lo + n))
    omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- The census, window by window. Each is an independent kernel check, so
the peak cost is one window's and not the whole enumeration's. -/
public theorem blkRange0 : blkCountRange 0 5 = 1227 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange1 : blkCountRange 5 5 = 528 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange2 : blkCountRange 10 5 = 410 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange3 : blkCountRange 15 5 = 457 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange4 : blkCountRange 20 5 = 33 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange5 : blkCountRange 25 5 = 297 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange6 : blkCountRange 30 5 = 33 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange7 : blkCountRange 35 5 = 132 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange8 : blkCountRange 40 5 = 17 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange9 : blkCountRange 45 5 = 16 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange10 : blkCountRange 50 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange11 : blkCountRange 55 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange12 : blkCountRange 60 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange13 : blkCountRange 65 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange14 : blkCountRange 70 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange15 : blkCountRange 75 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange16 : blkCountRange 80 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange17 : blkCountRange 85 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange18 : blkCountRange 90 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange19 : blkCountRange 95 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange20 : blkCountRange 100 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange21 : blkCountRange 105 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange22 : blkCountRange 110 5 = 0 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkRange23 : blkCountRange 115 5 = 0 := by decide +kernel

/-- `|Blk| = 3150`: the windows, composed. This is the computation half of
`T22`. -/
public theorem blkCount : blkCountUpTo 120 = 3150 := by
  have z : blkCountUpTo 0 = 0 := rfl
  have e0 : blkCountUpTo 5 = blkCountUpTo 0 + blkCountRange 0 5 :=
    blkCountUpTo_add 0 5
  have e1 : blkCountUpTo 10 = blkCountUpTo 5 + blkCountRange 5 5 :=
    blkCountUpTo_add 5 5
  have e2 : blkCountUpTo 15 = blkCountUpTo 10 + blkCountRange 10 5 :=
    blkCountUpTo_add 10 5
  have e3 : blkCountUpTo 20 = blkCountUpTo 15 + blkCountRange 15 5 :=
    blkCountUpTo_add 15 5
  have e4 : blkCountUpTo 25 = blkCountUpTo 20 + blkCountRange 20 5 :=
    blkCountUpTo_add 20 5
  have e5 : blkCountUpTo 30 = blkCountUpTo 25 + blkCountRange 25 5 :=
    blkCountUpTo_add 25 5
  have e6 : blkCountUpTo 35 = blkCountUpTo 30 + blkCountRange 30 5 :=
    blkCountUpTo_add 30 5
  have e7 : blkCountUpTo 40 = blkCountUpTo 35 + blkCountRange 35 5 :=
    blkCountUpTo_add 35 5
  have e8 : blkCountUpTo 45 = blkCountUpTo 40 + blkCountRange 40 5 :=
    blkCountUpTo_add 40 5
  have e9 : blkCountUpTo 50 = blkCountUpTo 45 + blkCountRange 45 5 :=
    blkCountUpTo_add 45 5
  have e10 : blkCountUpTo 55 = blkCountUpTo 50 + blkCountRange 50 5 :=
    blkCountUpTo_add 50 5
  have e11 : blkCountUpTo 60 = blkCountUpTo 55 + blkCountRange 55 5 :=
    blkCountUpTo_add 55 5
  have e12 : blkCountUpTo 65 = blkCountUpTo 60 + blkCountRange 60 5 :=
    blkCountUpTo_add 60 5
  have e13 : blkCountUpTo 70 = blkCountUpTo 65 + blkCountRange 65 5 :=
    blkCountUpTo_add 65 5
  have e14 : blkCountUpTo 75 = blkCountUpTo 70 + blkCountRange 70 5 :=
    blkCountUpTo_add 70 5
  have e15 : blkCountUpTo 80 = blkCountUpTo 75 + blkCountRange 75 5 :=
    blkCountUpTo_add 75 5
  have e16 : blkCountUpTo 85 = blkCountUpTo 80 + blkCountRange 80 5 :=
    blkCountUpTo_add 80 5
  have e17 : blkCountUpTo 90 = blkCountUpTo 85 + blkCountRange 85 5 :=
    blkCountUpTo_add 85 5
  have e18 : blkCountUpTo 95 = blkCountUpTo 90 + blkCountRange 90 5 :=
    blkCountUpTo_add 90 5
  have e19 : blkCountUpTo 100 = blkCountUpTo 95 + blkCountRange 95 5 :=
    blkCountUpTo_add 95 5
  have e20 : blkCountUpTo 105 = blkCountUpTo 100 + blkCountRange 100 5 :=
    blkCountUpTo_add 100 5
  have e21 : blkCountUpTo 110 = blkCountUpTo 105 + blkCountRange 105 5 :=
    blkCountUpTo_add 105 5
  have e22 : blkCountUpTo 115 = blkCountUpTo 110 + blkCountRange 110 5 :=
    blkCountUpTo_add 110 5
  have e23 : blkCountUpTo 120 = blkCountUpTo 115 + blkCountRange 115 5 :=
    blkCountUpTo_add 115 5
  have r0 := blkRange0
  have r1 := blkRange1
  have r2 := blkRange2
  have r3 := blkRange3
  have r4 := blkRange4
  have r5 := blkRange5
  have r6 := blkRange6
  have r7 := blkRange7
  have r8 := blkRange8
  have r9 := blkRange9
  have r10 := blkRange10
  have r11 := blkRange11
  have r12 := blkRange12
  have r13 := blkRange13
  have r14 := blkRange14
  have r15 := blkRange15
  have r16 := blkRange16
  have r17 := blkRange17
  have r18 := blkRange18
  have r19 := blkRange19
  have r20 := blkRange20
  have r21 := blkRange21
  have r22 := blkRange22
  have r23 := blkRange23
  omega

/-! ## The closure of an orthogonal quadruple is a block

The enumeration above counts closures. That a closure *is* a `D16` block is a
theorem, and it has to be one: a per-block `blockOK` certificate would ask the
kernel for `3150` reconstruction checks over `120` classes each, which is three
orders of magnitude more work than the enumeration itself. Proved once, the
per-block obligation drops to six inner products and a popcount.

The argument is Bessel's inequality, exact. For an orthogonal quadruple `q` of
class representatives and any root `y`, put

    u := 8y - sum_i <y,q_i> q_i.

Orthogonality gives `<u,q_k> = 0`, hence `<u,u> = 8 (8<y,y> - sum_i <y,q_i>^2)`,
and `<,>` is a sum of squares over `Z`, so

    sum_i <y,q_i>^2 = 64   iff   u = 0   iff   8y = sum_i <y,q_i> q_i,

which is exactly the reconstruction identity `D16`'s rank condition consumes
through `inSpan_of_recon`. For a class of the closure the sum is `64` twice
over: `64 + 0 + 0 + 0` for the four classes of the quadruple, and `4 * 16` for
a class adjacent to all four. So the closure has rank `4`, and if it also holds
twelve classes it is a block.
-/

/-- The closure of a quadruple written with the `Bitset` operations rather than
with `Nat.lor` and `Nat.land`. It is the same numeral -- `quadSet_eq` -- but
membership in it is `Bitset.mem_union` and `Bitset.mem_inter` rather than a
`testBit` computation, and every proof below is about membership. -/
@[expose] public def quadSet (a b c d : Nat) : Bitset :=
  Bitset.union
    (Bitset.inter (Bitset.inter (arow a) (arow b)) (Bitset.inter (arow c) (arow d)))
    (Bitset.union (Bitset.union (Bitset.singleton a) (Bitset.singleton b))
      (Bitset.union (Bitset.singleton c) (Bitset.singleton d)))

/-- `1 <<< a` and `2 ^ a` are the same set. The enumeration writes the shift
because it is one bignum call on the hot path; `Bitset.singleton` writes the
power because every core `testBit` lemma is stated about it. -/
public theorem shiftOne_eq (a : Nat) : Nat.shiftLeft 1 a = Bitset.singleton a := by
  show 1 <<< a = Nat.pow 2 a
  rw [Nat.shiftLeft_eq]
  exact Nat.one_mul _

/-- The two spellings of the closure agree, so the theorems below speak about
the set the enumeration counts. -/
public theorem quadSet_eq (a b c d : Nat) :
    Bitset.toNat (quadSet a b c d) = quadClosure a b c d := by
  simp only [quadSet, quadClosure, commonAdj, adjMask, arow, Bitset.toNat, Bitset.ofNat,
    Bitset.union, Bitset.inter, shiftOne_eq]

/-- A class lies in the closure exactly when it is adjacent to all four or is
one of the four. This is the bitset identity of the header, read back as a
statement about classes. -/
public theorem mem_quadSet (a b c d w : Nat) :
    w ∈ quadSet a b c d ↔
      ((w ∈ arow a ∧ w ∈ arow b ∧ w ∈ arow c ∧ w ∈ arow d)
        ∨ (w = a ∨ w = b ∨ w = c ∨ w = d)) := by
  simp only [quadSet]
  rw [Bitset.mem_union, Bitset.mem_inter, Bitset.mem_inter, Bitset.mem_inter,
    Bitset.mem_union, Bitset.mem_union, Bitset.mem_union,
    Bitset.mem_singleton, Bitset.mem_singleton, Bitset.mem_singleton, Bitset.mem_singleton]
  constructor
  · intro h
    rcases h with ⟨⟨h1, h2⟩, h3, h4⟩ | h1
    · exact Or.inl ⟨h1, h2, h3, h4⟩
    · rcases h1 with h2 | h2
      · rcases h2 with h3 | h3
        · exact Or.inr (Or.inl h3)
        · exact Or.inr (Or.inr (Or.inl h3))
      · rcases h2 with h3 | h3
        · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))
  · intro h
    rcases h with ⟨h1, h2, h3, h4⟩ | h1
    · exact Or.inl ⟨⟨h1, h2⟩, h3, h4⟩
    · rcases h1 with h2 | h2 | h2 | h2
      · exact Or.inr (Or.inl (Or.inl h2))
      · exact Or.inr (Or.inl (Or.inr h2))
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr h2))

/-- Adjacency is `|<u,v>| = 4`, recovered from the packed table's `0`/`1`. The
census reads adjacency off `adjRow`; the Bessel argument needs the inner
product itself, and this is the step that crosses between them. -/
public theorem dot_of_adjN {i j : Nat} (h : adjN i j = 1) :
    dot (repN i) (repN j) = 4 ∨ dot (repN i) (repN j) = -4 := by
  have hraw : ∀ p q : Nat, adjRaw p q = 1 →
      dot (repN p) (repN q) = 4 ∨ dot (repN p) (repN q) = -4 := by
    intro p q hpq
    by_cases h4 : dot8 (repN p) (repN q) = 4
    · exact Or.inl (by rw [← dot8_eq]; exact h4)
    · by_cases h4' : dot8 (repN p) (repN q) = -4
      · exact Or.inr (by rw [← dot8_eq]; exact h4')
      · have hr : adjRaw p q = (if dot8 (repN p) (repN q) = 4 then 1
            else if dot8 (repN p) (repN q) = -4 then 1 else 0) := rfl
        rw [hr, if_neg h4, if_neg h4'] at hpq
        exact absurd hpq (by decide)
  have hd : adjN i j = (if i = j then 0 else if i < j then adjRaw i j else adjRaw j i) := rfl
  by_cases hij : i = j
  · rw [hd, if_pos hij] at h
    exact absurd h (by decide)
  · rw [hd, if_neg hij] at h
    by_cases hlt : i < j
    · rw [if_pos hlt] at h
      exact hraw i j h
    · rw [if_neg hlt] at h
      rcases hraw j i h with hh | hh
      · exact Or.inl (by rw [dot_comm]; exact hh)
      · exact Or.inr (by rw [dot_comm]; exact hh)

public theorem dot_of_mem_arow {x w : Nat} (hx : x < 120) (hw : w < 120) (h : w ∈ arow x) :
    dot (repN x) (repN w) = 4 ∨ dot (repN x) (repN w) = -4 :=
  dot_of_adjN ((mem_adjRow hx hw).mp h)

/-- A single class below `120` is a class subset. -/
public theorem classSet_singleton {x : Nat} (hx : x < 120) : ClassSet (Bitset.singleton x) := by
  have hpos : 0 < (2 : Nat) ^ x := Nat.two_pow_pos x
  have hle : (2 : Nat) ^ (x + 1) ≤ 2 ^ 120 := Nat.pow_le_pow_right (by decide) (by omega)
  have hstep : (2 : Nat) ^ (x + 1) = 2 ^ x * 2 := Nat.pow_succ 2 x
  show Bitset.toNat (Bitset.singleton x) < 2 ^ 120
  rw [Bitset.singleton_toNat]
  omega

/-- The closure is a class subset: the common adjacency is cut out of one
adjacency row, and the four classes are singletons below `120`. -/
public theorem classSet_quadSet {a b c d : Nat}
    (ha : a < 120) (hb : b < 120) (hc : c < 120) (hd : d < 120) :
    ClassSet (quadSet a b c d) := by
  refine classSet_union (classSet_inter (classSet_inter (classSet_arow a))) ?_
  exact classSet_union (classSet_union (classSet_singleton ha) (classSet_singleton hb))
    (classSet_union (classSet_singleton hc) (classSet_singleton hd))

/-- The quadruple as a function on `Fin 4`, which is the shape `HasRank` asks
its basis to have. -/
@[expose] public def quadIdx (a b c d : Nat) : Fin 4 → Nat
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d

/-- The four class representatives, the candidate basis of the block. -/
@[expose] public def quadBasis (a b c d : Nat) : Fin 4 → Vec 8 Int :=
  fun i => repN (quadIdx a b c d i)

/-- Case analysis on `Fin 4`, written out once: sixteen Gram entries and four
basis conditions are all checked index by index below. -/
public theorem fin4 {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ i : Fin 4, P i
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3

/-- An adjacent pair contributes `16` to the Bessel sum, whichever sign the
pairing takes. -/
public theorem sq_of_adj {p q : Nat}
    (h : dot (repN p) (repN q) = 4 ∨ dot (repN p) (repN q) = -4) :
    dot (repN q) (repN p) * dot (repN q) (repN p) = 16 := by
  rw [dot_comm (repN q) (repN p)]
  rcases h with h | h <;> rw [h] <;> decide

/-- A sum over `Fin 4`, written out. Every sum in the Bessel argument has four
terms, and four explicit terms are what `omega` can rearrange. -/
public theorem sumInt4 (f : Vec 4 Int) : Vec.sumInt f = f 0 + f 1 + f 2 + f 3 := by
  show f 0 + (f 1 + (f 2 + (f 3 + 0))) = f 0 + f 1 + f 2 + f 3
  omega

/-- `sum_i c_i b_i`, built from the library's `add` and `smul` so that the
`dot` lemmas apply to it without unfolding anything. -/
@[expose] public def comb4 (c : Fin 4 → Int) (b : Fin 4 → Vec 8 Int) : Vec 8 Int :=
  AddCommGroup.add
    (AddCommGroup.add (Vec.smul (c 0) (b 0)) (Vec.smul (c 1) (b 1)))
    (AddCommGroup.add (Vec.smul (c 2) (b 2)) (Vec.smul (c 3) (b 3)))

public theorem dot_comb4_left (c : Fin 4 → Int) (b : Fin 4 → Vec 8 Int) (v : Vec 8 Int) :
    dot (comb4 c b) v
      = c 0 * dot (b 0) v + c 1 * dot (b 1) v + c 2 * dot (b 2) v + c 3 * dot (b 3) v := by
  show dot (AddCommGroup.add
    (AddCommGroup.add (Vec.smul (c 0) (b 0)) (Vec.smul (c 1) (b 1)))
    (AddCommGroup.add (Vec.smul (c 2) (b 2)) (Vec.smul (c 3) (b 3)))) v = _
  rw [dot_add_left, dot_add_left, dot_add_left, dot_smul_left, dot_smul_left,
    dot_smul_left, dot_smul_left]
  omega

public theorem dot_comb4_right (c : Fin 4 → Int) (b : Fin 4 → Vec 8 Int) (v : Vec 8 Int) :
    dot v (comb4 c b)
      = c 0 * dot v (b 0) + c 1 * dot v (b 1) + c 2 * dot v (b 2) + c 3 * dot v (b 3) := by
  rw [dot_comm v (comb4 c b), dot_comb4_left, dot_comm (b 0) v, dot_comm (b 1) v,
    dot_comm (b 2) v, dot_comm (b 3) v]

/-- The Bessel residue `8y - sum_i <y,b_i> b_i`. -/
@[expose] public def bessel (b : Fin 4 → Vec 8 Int) (y : Vec 8 Int) : Vec 8 Int :=
  AddCommGroup.add (Vec.smul 8 y) (AddCommGroup.neg (comb4 (fun i => dot y (b i)) b))

public theorem dot_bessel_left (b : Fin 4 → Vec 8 Int) (y v : Vec 8 Int) :
    dot (bessel b y) v = 8 * dot y v
      - (dot y (b 0) * dot (b 0) v + dot y (b 1) * dot (b 1) v
        + dot y (b 2) * dot (b 2) v + dot y (b 3) * dot (b 3) v) := by
  show dot (AddCommGroup.add (Vec.smul 8 y)
    (AddCommGroup.neg (comb4 (fun i => dot y (b i)) b))) v = _
  rw [dot_add_left, dot_neg_left, dot_smul_left, dot_comb4_left]
  omega

/-- The form is positive definite over `Z` for the cheapest possible reason:
`<x,x>` is a sum of squares, so it vanishes only at `0`. This is what turns the
Bessel bound into an equality rather than an inequality. -/
public theorem dot_self_zero {x : Vec 8 Int} (h : dot x x = 0) (j : Fin 8) : x j = 0 := by
  have hnn : ∀ i : Fin 8, 0 ≤ x i * x i := fun i => mul_self_nonneg (x i)
  have hle : x j * x j ≤ Vec.sumInt (fun i : Fin 8 => x i * x i) :=
    sumInt_term_le (fun i : Fin 8 => x i * x i) hnn j
  have hd : Vec.sumInt (fun i : Fin 8 => x i * x i) = 0 := h
  have h0 : x j * x j = 0 := by
    have := hnn j
    omega
  rcases Int.mul_eq_zero.mp h0 with h1 | h1
  · exact h1
  · exact h1

/-- The Bessel equality. A root whose squared pairings against an orthogonal
quadruple of norm-`8` vectors sum to `64` reconstructs from that quadruple, and
`inSpan_of_recon` then places it in the quadruple's span. -/
public theorem recon_of_parseval {b : Fin 4 → Vec 8 Int}
    (horth : ∀ i j : Fin 4, dot (b i) (b j) = if i = j then 8 else 0)
    {y : Vec 8 Int} (hy : dot y y = 8)
    (hS : dot y (b 0) * dot y (b 0) + dot y (b 1) * dot y (b 1)
        + dot y (b 2) * dot y (b 2) + dot y (b 3) * dot y (b 3) = 64) :
    Recon b y := by
  have e00 : dot (b 0) (b 0) = 8 := by rw [horth 0 0]; exact if_pos rfl
  have e11 : dot (b 1) (b 1) = 8 := by rw [horth 1 1]; exact if_pos rfl
  have e22 : dot (b 2) (b 2) = 8 := by rw [horth 2 2]; exact if_pos rfl
  have e33 : dot (b 3) (b 3) = 8 := by rw [horth 3 3]; exact if_pos rfl
  have e01 : dot (b 0) (b 1) = 0 := by rw [horth 0 1]; exact if_neg (by decide)
  have e02 : dot (b 0) (b 2) = 0 := by rw [horth 0 2]; exact if_neg (by decide)
  have e03 : dot (b 0) (b 3) = 0 := by rw [horth 0 3]; exact if_neg (by decide)
  have e10 : dot (b 1) (b 0) = 0 := by rw [horth 1 0]; exact if_neg (by decide)
  have e12 : dot (b 1) (b 2) = 0 := by rw [horth 1 2]; exact if_neg (by decide)
  have e13 : dot (b 1) (b 3) = 0 := by rw [horth 1 3]; exact if_neg (by decide)
  have e20 : dot (b 2) (b 0) = 0 := by rw [horth 2 0]; exact if_neg (by decide)
  have e21 : dot (b 2) (b 1) = 0 := by rw [horth 2 1]; exact if_neg (by decide)
  have e23 : dot (b 2) (b 3) = 0 := by rw [horth 2 3]; exact if_neg (by decide)
  have e30 : dot (b 3) (b 0) = 0 := by rw [horth 3 0]; exact if_neg (by decide)
  have e31 : dot (b 3) (b 1) = 0 := by rw [horth 3 1]; exact if_neg (by decide)
  have e32 : dot (b 3) (b 2) = 0 := by rw [horth 3 2]; exact if_neg (by decide)
  have hub : ∀ k : Fin 4, dot (bessel b y) (b k) = 0 := by
    refine fin4 ?_ ?_ ?_ ?_
    · rw [dot_bessel_left, e00, e10, e20, e30]; omega
    · rw [dot_bessel_left, e01, e11, e21, e31]; omega
    · rw [dot_bessel_left, e02, e12, e22, e32]; omega
    · rw [dot_bessel_left, e03, e13, e23, e33]; omega
  have huy : dot (bessel b y) y = 0 := by
    rw [dot_bessel_left, dot_comm (b 0) y, dot_comm (b 1) y, dot_comm (b 2) y,
      dot_comm (b 3) y, hy]
    omega
  have huu : dot (bessel b y) (bessel b y) = 0 := by
    show dot (bessel b y) (AddCommGroup.add (Vec.smul 8 y)
      (AddCommGroup.neg (comb4 (fun i => dot y (b i)) b))) = 0
    rw [dot_add_right, dot_neg_right, dot_smul_right, dot_comb4_right, huy,
      hub 0, hub 1, hub 2, hub 3]
    omega
  intro j
  have hz : bessel b y j = 0 := dot_self_zero huu j
  have hb : bessel b y j
      = 8 * y j - ((dot y (b 0) * b 0 j + dot y (b 1) * b 1 j)
        + (dot y (b 2) * b 2 j + dot y (b 3) * b 3 j)) := rfl
  have hsum : Vec.sumInt (fun i : Fin 4 => dot y (b i) * b i j)
      = dot y (b 0) * b 0 j + dot y (b 1) * b 1 j + dot y (b 2) * b 2 j
        + dot y (b 3) * b 3 j := sumInt4 _
  rw [hsum]
  omega

/-- The Gram matrix of the quadruple: `8` on the diagonal because a class
representative is a root, `0` off it by hypothesis. This is the input both
`indep_of_orth` and `recon_of_parseval` take. -/
public theorem quad_gram {a b c d : Nat}
    (ha : a < 120) (hb : b < 120) (hc : c < 120) (hd : d < 120)
    (oab : dot (repN a) (repN b) = 0) (oac : dot (repN a) (repN c) = 0)
    (oad : dot (repN a) (repN d) = 0) (obc : dot (repN b) (repN c) = 0)
    (obd : dot (repN b) (repN d) = 0) (ocd : dot (repN c) (repN d) = 0) :
    ∀ i j : Fin 4,
      dot (quadBasis a b c d i) (quadBasis a b c d j) = if i = j then 8 else 0 := by
  have oba : dot (repN b) (repN a) = 0 := by rw [dot_comm (repN b) (repN a)]; exact oab
  have oca : dot (repN c) (repN a) = 0 := by rw [dot_comm (repN c) (repN a)]; exact oac
  have oda : dot (repN d) (repN a) = 0 := by rw [dot_comm (repN d) (repN a)]; exact oad
  have ocb : dot (repN c) (repN b) = 0 := by rw [dot_comm (repN c) (repN b)]; exact obc
  have odb : dot (repN d) (repN b) = 0 := by rw [dot_comm (repN d) (repN b)]; exact obd
  have odc : dot (repN d) (repN c) = 0 := by rw [dot_comm (repN d) (repN c)]; exact ocd
  have na : dot (repN a) (repN a) = 8 := (D11_repN ha).2
  have nb : dot (repN b) (repN b) = 8 := (D11_repN hb).2
  have nc : dot (repN c) (repN c) = 8 := (D11_repN hc).2
  have nd : dot (repN d) (repN d) = 8 := (D11_repN hd).2
  refine fin4 ?_ ?_ ?_ ?_
  · refine fin4 ?_ ?_ ?_ ?_
    · show dot (repN a) (repN a) = if (0 : Fin 4) = (0 : Fin 4) then 8 else 0
      rw [if_pos rfl]; exact na
    · show dot (repN a) (repN b) = if (0 : Fin 4) = (1 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact oab
    · show dot (repN a) (repN c) = if (0 : Fin 4) = (2 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact oac
    · show dot (repN a) (repN d) = if (0 : Fin 4) = (3 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact oad
  · refine fin4 ?_ ?_ ?_ ?_
    · show dot (repN b) (repN a) = if (1 : Fin 4) = (0 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact oba
    · show dot (repN b) (repN b) = if (1 : Fin 4) = (1 : Fin 4) then 8 else 0
      rw [if_pos rfl]; exact nb
    · show dot (repN b) (repN c) = if (1 : Fin 4) = (2 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact obc
    · show dot (repN b) (repN d) = if (1 : Fin 4) = (3 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact obd
  · refine fin4 ?_ ?_ ?_ ?_
    · show dot (repN c) (repN a) = if (2 : Fin 4) = (0 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact oca
    · show dot (repN c) (repN b) = if (2 : Fin 4) = (1 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact ocb
    · show dot (repN c) (repN c) = if (2 : Fin 4) = (2 : Fin 4) then 8 else 0
      rw [if_pos rfl]; exact nc
    · show dot (repN c) (repN d) = if (2 : Fin 4) = (3 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact ocd
  · refine fin4 ?_ ?_ ?_ ?_
    · show dot (repN d) (repN a) = if (3 : Fin 4) = (0 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact oda
    · show dot (repN d) (repN b) = if (3 : Fin 4) = (1 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact odb
    · show dot (repN d) (repN c) = if (3 : Fin 4) = (2 : Fin 4) then 8 else 0
      rw [if_neg (by decide)]; exact odc
    · show dot (repN d) (repN d) = if (3 : Fin 4) = (3 : Fin 4) then 8 else 0
      rw [if_pos rfl]; exact nd

/-- Every class of the closure reconstructs from the quadruple: the Bessel sum
is `64 + 0 + 0 + 0` for the four classes themselves and `4 * 16` for a class
adjacent to all four, and there is no other way for a class of the closure to
arise. -/
public theorem recon_of_mem_quadSet {a b c d : Nat}
    (ha : a < 120) (hb : b < 120) (hc : c < 120) (hd : d < 120)
    (oab : dot (repN a) (repN b) = 0) (oac : dot (repN a) (repN c) = 0)
    (oad : dot (repN a) (repN d) = 0) (obc : dot (repN b) (repN c) = 0)
    (obd : dot (repN b) (repN d) = 0) (ocd : dot (repN c) (repN d) = 0)
    {w : Nat} (hw : w < 120) (hwm : w ∈ quadSet a b c d) :
    Recon (quadBasis a b c d) (repN w) := by
  have oba : dot (repN b) (repN a) = 0 := by rw [dot_comm (repN b) (repN a)]; exact oab
  have oca : dot (repN c) (repN a) = 0 := by rw [dot_comm (repN c) (repN a)]; exact oac
  have oda : dot (repN d) (repN a) = 0 := by rw [dot_comm (repN d) (repN a)]; exact oad
  have ocb : dot (repN c) (repN b) = 0 := by rw [dot_comm (repN c) (repN b)]; exact obc
  have odb : dot (repN d) (repN b) = 0 := by rw [dot_comm (repN d) (repN b)]; exact obd
  have odc : dot (repN d) (repN c) = 0 := by rw [dot_comm (repN d) (repN c)]; exact ocd
  have na : dot (repN a) (repN a) = 8 := (D11_repN ha).2
  have nb : dot (repN b) (repN b) = 8 := (D11_repN hb).2
  have nc : dot (repN c) (repN c) = 8 := (D11_repN hc).2
  have nd : dot (repN d) (repN d) = 8 := (D11_repN hd).2
  refine recon_of_parseval (quad_gram ha hb hc hd oab oac oad obc obd ocd)
    (D11_repN hw).2 ?_
  show dot (repN w) (repN a) * dot (repN w) (repN a)
    + dot (repN w) (repN b) * dot (repN w) (repN b)
    + dot (repN w) (repN c) * dot (repN w) (repN c)
    + dot (repN w) (repN d) * dot (repN w) (repN d) = 64
  rcases (mem_quadSet a b c d w).mp hwm with ⟨m1, m2, m3, m4⟩ | he
  · have s0 := sq_of_adj (dot_of_mem_arow ha hw m1)
    have s1 := sq_of_adj (dot_of_mem_arow hb hw m2)
    have s2 := sq_of_adj (dot_of_mem_arow hc hw m3)
    have s3 := sq_of_adj (dot_of_mem_arow hd hw m4)
    omega
  · rcases he with h | h | h | h
    · subst h; rw [na, oab, oac, oad]; decide
    · subst h; rw [oba, nb, obc, obd]; decide
    · subst h; rw [oca, ocb, nc, ocd]; decide
    · subst h; rw [oda, odb, odc, nd]; decide

/-- Four pairwise orthogonal classes whose closure holds twelve classes close
to a `D16` block. The rank condition is discharged by the quadruple itself:
orthogonal representatives of norm `8` are independent by `indep_of_orth`, and
every class of the closure reconstructs from them. -/
public theorem block_of_quad {a b c d : Nat}
    (ha : a < 120) (hb : b < 120) (hc : c < 120) (hd : d < 120)
    (oab : dot (repN a) (repN b) = 0) (oac : dot (repN a) (repN c) = 0)
    (oad : dot (repN a) (repN d) = 0) (obc : dot (repN b) (repN c) = 0)
    (obd : dot (repN b) (repN d) = 0) (ocd : dot (repN c) (repN d) = 0)
    (hcard : Bitset.card (quadSet a b c d) = 12) :
    D16 (quadSet a b c d) := by
  have horth := quad_gram ha hb hc hd oab oac oad obc obd ocd
  have hmemA : a ∈ quadSet a b c d := (mem_quadSet a b c d a).mpr (Or.inr (Or.inl rfl))
  have hmemB : b ∈ quadSet a b c d :=
    (mem_quadSet a b c d b).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hmemC : c ∈ quadSet a b c d :=
    (mem_quadSet a b c d c).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hmemD : d ∈ quadSet a b c d :=
    (mem_quadSet a b c d d).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hlt : ∀ i : Fin 4, quadIdx a b c d i < 120 := fin4 ha hb hc hd
  have hmem : ∀ i : Fin 4, quadIdx a b c d i ∈ quadSet a b c d :=
    fin4 hmemA hmemB hmemC hmemD
  refine ⟨classSet_quadSet ha hb hc hd, hcard, quadBasis a b c d, ?_,
    indep_of_orth _ horth, ?_⟩
  · intro i
    refine ⟨D11_repN (hlt i), ?_⟩
    show (D12 (repN (quadIdx a b c d i))).val ∈ quadSet a b c d
    rw [D12_repN (hlt i)]
    exact hmem i
  · intro x hx
    obtain ⟨hxR, hxB⟩ := hx
    refine inSpan_of_recon _ _ ?_
    have hc120 : (D12 x).val < 120 := (D12 x).isLt
    have hrep : repN (D12 x).val = nrm x := rep_D12 hxR
    have hR : Recon (quadBasis a b c d) (repN (D12 x).val) :=
      recon_of_mem_quadSet ha hb hc hd oab oac oad obc obd ocd hc120 hxB
    by_cases hpos : 0 < dot x posRef
    · have h1 : nrm x = x := if_pos hpos
      rw [h1] at hrep
      exact hrep ▸ hR
    · have hne : nrm x = AddCommGroup.neg x := if_neg hpos
      rw [hne] at hrep
      have hx2 : AddCommGroup.neg (repN (D12 x).val) = x := by
        rw [hrep]; exact vneg_neg x
      exact hx2 ▸ hR.neg

/-- The per-entry certificate: four class indices, pairwise orthogonal, whose
closure holds twelve classes. Six inner products and a popcount, which is what
makes `3150` of these affordable where `3150` reconstruction sweeps are not. -/
@[expose] public def quadOK (a b c d : Nat) : Bool :=
  decide (a < 120) && decide (b < 120) && decide (c < 120) && decide (d < 120)
    && decide (dot8 (repN a) (repN b) = 0) && decide (dot8 (repN a) (repN c) = 0)
    && decide (dot8 (repN a) (repN d) = 0) && decide (dot8 (repN b) (repN c) = 0)
    && decide (dot8 (repN b) (repN d) = 0) && decide (dot8 (repN c) (repN d) = 0)
    && decide (Bitset.card (quadSet a b c d) = 12)

public theorem block_of_quadOK {a b c d : Nat} (h : quadOK a b c d = true) :
    D16 (quadSet a b c d) := by
  simp only [quadOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact block_of_quad h1 h2 h3 h4
    (by rw [← dot8_eq]; exact h5) (by rw [← dot8_eq]; exact h6)
    (by rw [← dot8_eq]; exact h7) (by rw [← dot8_eq]; exact h8)
    (by rw [← dot8_eq]; exact h9) (by rw [← dot8_eq]; exact h10) h11

/-! ## The closure is exactly the classes of the span

The header's identity `closure(q) = q u (adj(q_0) n ... n adj(q_3))` is a claim
about *which classes lie in the span of `q`*, and the enumeration is only a
census of blocks if that claim is a theorem. `block_of_quad` proved one
direction: a class of the closure reconstructs from `q`. This section proves
the other, and it is Bessel's inequality again, now read as a bound rather than
as an equality: a class in the span pairs with `q` to `sum_i <v,q_i>^2 = 64`,
every summand is `0`, `16` or `64` because the pairing values are `0`, `+-4`
and `8`, and `64` is reached only by `64 + 0 + 0 + 0` -- the class is one of the
four -- or by `16 + 16 + 16 + 16` -- the class is adjacent to all four. There
is no third way, so the span adds nothing to the closure. -/

public theorem dot_tri {i j : Nat} (hi : i < 120) (hj : j < 120) (hne : i ≠ j) :
    dot (repN i) (repN j) = 0 ∨ dot (repN i) (repN j) = 4
      ∨ dot (repN i) (repN j) = -4 := by
  have h := allLt_true _ _ (allLt_true _ _ dotTri i hi) j hj
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with ((h1 | h1) | h1) | h1
  · exact absurd (of_decide_eq_true h1) hne
  · exact Or.inl (by rw [← dot8_eq]; exact of_decide_eq_true h1)
  · exact Or.inr (Or.inl (by rw [← dot8_eq]; exact of_decide_eq_true h1))
  · exact Or.inr (Or.inr (by rw [← dot8_eq]; exact of_decide_eq_true h1))

/-- Adjacency read the other way: a pairing of `+-4` puts the class in the row.
`block_of_quad` needed the row to give the pairing; the span direction needs
the pairing to give the row. -/
public theorem adjN_of_dot {i j : Nat} (hne : i ≠ j)
    (h : dot (repN i) (repN j) = 4 ∨ dot (repN i) (repN j) = -4) : adjN i j = 1 := by
  have hraw : ∀ p q : Nat, (dot (repN p) (repN q) = 4 ∨ dot (repN p) (repN q) = -4) →
      adjRaw p q = 1 := by
    intro p q hpq
    have hr : adjRaw p q = (if dot8 (repN p) (repN q) = 4 then 1
        else if dot8 (repN p) (repN q) = -4 then 1 else 0) := rfl
    rcases hpq with h4 | h4
    · rw [hr, if_pos (by rw [dot8_eq]; exact h4)]
    · rw [hr, if_neg (by rw [dot8_eq, h4]; decide), if_pos (by rw [dot8_eq]; exact h4)]
  have hd : adjN i j = (if i = j then 0 else if i < j then adjRaw i j else adjRaw j i) := rfl
  rw [hd, if_neg hne]
  by_cases hlt : i < j
  · rw [if_pos hlt]
    exact hraw i j h
  · rw [if_neg hlt]
    refine hraw j i ?_
    rcases h with hh | hh
    · exact Or.inl (by rw [dot_comm]; exact hh)
    · exact Or.inr (by rw [dot_comm]; exact hh)

public theorem mem_arow_of_dot {i j : Nat} (hi : i < 120) (hj : j < 120) (hne : i ≠ j)
    (h : dot (repN i) (repN j) = 4 ∨ dot (repN i) (repN j) = -4) : j ∈ arow i :=
  (mem_adjRow hi hj).mpr (adjN_of_dot hne h)

/-- Bessel, the other way round: a root in the span of an orthogonal quadruple
of norm-`8` vectors pairs with it to squared sum `64`. Over `Q`, because the
coefficients are `<v,q_i>/8` and that is where the division lives. -/
public theorem parseval_of_inSpan {b : Fin 4 → Vec 8 Int}
    (horth : ∀ i j : Fin 4, dot (b i) (b j) = if i = j then 8 else 0)
    {y : Vec 8 Int} (hy : dot y y = 8) (h : InSpan b (qOf y)) :
    dot y (b 0) * dot y (b 0) + dot y (b 1) * dot y (b 1)
      + dot y (b 2) * dot y (b 2) + dot y (b 3) * dot y (b 3) = 64 := by
  obtain ⟨c, hc⟩ := h
  have hq : qOf y = qComb b c := funext hc
  have key : ∀ i : Fin 4,
      ((dot y (b i) : Int) : Rat) = mul (c i) (((8 : Int) : Rat)) := by
    intro i
    have h1 : Vec.inner (qComb b c) (qOf (b i)) = ((dot y (b i) : Int) : Rat) := by
      rw [← hq]
      exact inner_qOf y (b i)
    rw [inner_qComb] at h1
    have h2 : ∀ j : Fin 4, mul (c j) (Vec.inner (qOf (b j)) (qOf (b i)))
        = (if i = j then mul (c j) (((8 : Int) : Rat)) else zero) := by
      intro j
      rw [inner_qOf, horth j i]
      by_cases hji : j = i
      · rw [if_pos hji, if_pos hji.symm]
      · rw [if_neg hji, if_neg (fun hh => hji hh.symm)]
        exact mul_zero (c j)
    rw [Vec.sum_congr h2, Vec.sum_ite_eq i (fun j => mul (c j) (((8 : Int) : Rat)))] at h1
    exact h1.symm
  have h1 : Vec.inner (qComb b c) (qOf y) = ((dot y y : Int) : Rat) := by
    rw [← hq]
    exact inner_qOf y y
  rw [inner_qComb] at h1
  have h2 : ∀ i : Fin 4, Vec.inner (qOf (b i)) (qOf y) = ((dot y (b i) : Int) : Rat) := by
    intro i
    rw [inner_qOf, dot_comm (b i) y]
  rw [Vec.sum_congr (fun i => congrArg (mul (c i)) (h2 i)), hy] at h1
  have h3 : mul (((8 : Int) : Rat))
        (Vec.sum (fun i : Fin 4 => mul (c i) ((dot y (b i) : Int) : Rat)))
      = Vec.sum (fun i : Fin 4 =>
          mul ((dot y (b i) : Int) : Rat) ((dot y (b i) : Int) : Rat)) := by
    rw [Vec.mul_sum]
    refine Vec.sum_congr (fun i => ?_)
    rw [← mul_assoc, mul_comm (((8 : Int) : Rat)) (c i), ← key i]
  have h4 : Vec.sum (fun i : Fin 4 =>
        mul ((dot y (b i) : Int) : Rat) ((dot y (b i) : Int) : Rat))
      = ((Vec.sumInt (fun i : Fin 4 => dot y (b i) * dot y (b i)) : Int) : Rat) := by
    rw [Vec.sumInt_eq_sum]
    refine Eq.trans ?_ (hom_map_sum NumInstances.intToRat
      (fun i : Fin 4 => dot y (b i) * dot y (b i))).symm
    exact Vec.sum_congr (fun i => (Rat.intCast_mul (dot y (b i)) (dot y (b i))).symm)
  rw [h1, h4] at h3
  have h5 : (((8 * 8 : Int)) : Rat)
      = ((Vec.sumInt (fun i : Fin 4 => dot y (b i) * dot y (b i)) : Int) : Rat) := by
    rw [Rat.intCast_mul]
    exact h3
  have h6 : (8 * 8 : Int) = Vec.sumInt (fun i : Fin 4 => dot y (b i) * dot y (b i)) :=
    Rat.intCast_inj.mp h5
  rw [sumInt4 (fun i : Fin 4 => dot y (b i) * dot y (b i))] at h6
  omega

/-- The span adds nothing to the closure: a class whose representative lies in
the span of the quadruple is already in the closure. With `block_of_quad`'s
`hclass` this makes the closure *exactly* the classes of the span, which is the
identity the enumeration is built on. -/
public theorem mem_quadSet_of_inSpan {a b c d : Nat}
    (ha : a < 120) (hb : b < 120) (hc : c < 120) (hd : d < 120)
    (oab : dot (repN a) (repN b) = 0) (oac : dot (repN a) (repN c) = 0)
    (oad : dot (repN a) (repN d) = 0) (obc : dot (repN b) (repN c) = 0)
    (obd : dot (repN b) (repN d) = 0) (ocd : dot (repN c) (repN d) = 0)
    {w : Nat} (hw : w < 120)
    (hs : InSpan (quadBasis a b c d) (qOf (repN w))) :
    w ∈ quadSet a b c d := by
  have horth : ∀ i j : Fin 4,
      dot (quadBasis a b c d i) (quadBasis a b c d j) = if i = j then 8 else 0 :=
    quad_gram ha hb hc hd oab oac oad obc obd ocd
  have hS := parseval_of_inSpan horth (D11_repN hw).2 hs
  have hS' : dot (repN w) (repN a) * dot (repN w) (repN a)
      + dot (repN w) (repN b) * dot (repN w) (repN b)
      + dot (repN w) (repN c) * dot (repN w) (repN c)
      + dot (repN w) (repN d) * dot (repN w) (repN d) = 64 := hS
  by_cases hwa : w = a
  · exact (mem_quadSet a b c d w).mpr (Or.inr (Or.inl hwa))
  by_cases hwb : w = b
  · exact (mem_quadSet a b c d w).mpr (Or.inr (Or.inr (Or.inl hwb)))
  by_cases hwc : w = c
  · exact (mem_quadSet a b c d w).mpr (Or.inr (Or.inr (Or.inr (Or.inl hwc))))
  by_cases hwd : w = d
  · exact (mem_quadSet a b c d w).mpr (Or.inr (Or.inr (Or.inr (Or.inr hwd))))
  have ta := dot_tri hw ha hwa
  have tb := dot_tri hw hb hwb
  have tc := dot_tri hw hc hwc
  have td := dot_tri hw hd hwd
  have sqa : dot (repN w) (repN a) * dot (repN w) (repN a) ≤ 16 := by
    rcases ta with h | h | h <;> rw [h] <;> decide
  have sqb : dot (repN w) (repN b) * dot (repN w) (repN b) ≤ 16 := by
    rcases tb with h | h | h <;> rw [h] <;> decide
  have sqc : dot (repN w) (repN c) * dot (repN w) (repN c) ≤ 16 := by
    rcases tc with h | h | h <;> rw [h] <;> decide
  have sqd : dot (repN w) (repN d) * dot (repN w) (repN d) ≤ 16 := by
    rcases td with h | h | h <;> rw [h] <;> decide
  have pa : dot (repN w) (repN a) = 4 ∨ dot (repN w) (repN a) = -4 := by
    rcases ta with h | h | h
    · rw [h] at hS'; omega
    · exact Or.inl h
    · exact Or.inr h
  have pb : dot (repN w) (repN b) = 4 ∨ dot (repN w) (repN b) = -4 := by
    rcases tb with h | h | h
    · rw [h] at hS'; omega
    · exact Or.inl h
    · exact Or.inr h
  have pc : dot (repN w) (repN c) = 4 ∨ dot (repN w) (repN c) = -4 := by
    rcases tc with h | h | h
    · rw [h] at hS'; omega
    · exact Or.inl h
    · exact Or.inr h
  have pd : dot (repN w) (repN d) = 4 ∨ dot (repN w) (repN d) = -4 := by
    rcases td with h | h | h
    · rw [h] at hS'; omega
    · exact Or.inl h
    · exact Or.inr h
  refine (mem_quadSet a b c d w).mpr (Or.inl ⟨?_, ?_, ?_, ?_⟩)
  · refine mem_arow_of_dot ha hw (fun hh => hwa hh.symm) ?_
    rcases pa with h | h
    · exact Or.inl (by rw [dot_comm]; exact h)
    · exact Or.inr (by rw [dot_comm]; exact h)
  · refine mem_arow_of_dot hb hw (fun hh => hwb hh.symm) ?_
    rcases pb with h | h
    · exact Or.inl (by rw [dot_comm]; exact h)
    · exact Or.inr (by rw [dot_comm]; exact h)
  · refine mem_arow_of_dot hc hw (fun hh => hwc hh.symm) ?_
    rcases pc with h | h
    · exact Or.inl (by rw [dot_comm]; exact h)
    · exact Or.inr (by rw [dot_comm]; exact h)
  · refine mem_arow_of_dot hd hw (fun hh => hwd hh.symm) ?_
    rcases pd with h | h
    · exact Or.inl (by rw [dot_comm]; exact h)
    · exact Or.inr (by rw [dot_comm]; exact h)

/-- The closure of an orthogonal quadruple is exactly the set of classes whose
representative lies in its span. This is the identity the module header states
and the enumeration is built on: with it, "closure" is not a name for a bitset
expression but for the span, and a twelve-class closure is a block by
`block_of_quad`. -/
public theorem mem_quadSet_iff_inSpan {a b c d : Nat}
    (ha : a < 120) (hb : b < 120) (hc : c < 120) (hd : d < 120)
    (oab : dot (repN a) (repN b) = 0) (oac : dot (repN a) (repN c) = 0)
    (oad : dot (repN a) (repN d) = 0) (obc : dot (repN b) (repN c) = 0)
    (obd : dot (repN b) (repN d) = 0) (ocd : dot (repN c) (repN d) = 0)
    {w : Nat} (hw : w < 120) :
    w ∈ quadSet a b c d ↔ InSpan (quadBasis a b c d) (qOf (repN w)) := by
  constructor
  · intro h
    exact inSpan_of_recon _ _
      (recon_of_mem_quadSet ha hb hc hd oab oac oad obc obd ocd hw h)
  · exact mem_quadSet_of_inSpan ha hb hc hd oab oac oad obc obd ocd hw

/-! ## The `3150` blocks, exhibited

The blocks themselves, as a table rather than as a count. Each entry is the
orthogonal quadruple that generates one block, four seven-bit fields in one
`28`-bit word, and the table is one numeral rather than a list because a list
of `3150` entries is a term the kernel would have to walk to reach any one of
them. The entries are ordered by the numeral of the block they close, so the
table's own order certifies that the `3150` blocks are distinct: consecutive
closures increase, and `blkLt` propagates that to every pair.

`quadOK` is the per-entry certificate `block_of_quad` consumes: four class
indices, pairwise orthogonal, closing to twelve classes. Nothing about the
enumeration above is assumed here -- this table stands on `block_of_quad`, and
`blkCount` stands on the windows, and the two meet only in the number `3150`.
-/

/-- The table in `280`-bit words, ten quadruples to a word, exactly as
`repWords` carries the class representatives. The words are assembled into one
numeral below; the kernel evaluates that numeral once and reads every entry out
of the result. -/
@[expose] public def blkWords : List Nat :=
  [
    0x4e981824e980804a9078e4a901824a90080468808042800803e780803a700803668080,
    0x5ab078e5ab01825ab008056a878e56a818256a808052a078e52a018252a00804e9878e,
    0x62c00805eb8d9a5eb88905eb82845eb878e5eb81825eb80805ab0d9a5ab08905ab0284,
    0x66c889066c828466c878e66c818266c808062c0d9a62c089062c028462c078e62c0182,
    0x6ad08906ad02846ad078e6ad01826ad008066c92a466c8e9c66c899266c838666c8d9a,
    0x6ed88906ed82846ed878e6ed81826ed80806ad12a46ad0e9c6ad09926ad03866ad0d9a,
    0x6ed96ac6ed93a66ed8f9e6ed8a946ed84886ed92a46ed8e9c6ed89926ed83866ed8d9a,
    0x88e9aa588e5ba582e9b2680edb2686e1ba784e5ba77ae9b2c78edb2c7ee1bad7ce5bad,
    0x80f9a248cedb258ce59258ce1aa582f1b2480f5b248aeda258ae99258ae1ba588ed9a5,
    0x84f592482f99248ee9b258ee5a258ee19a58d05b2d8cf5b2786f19a480fd9a484f1a24,
    0x8b09bac8af9ba6890dbac88fdba686f9ba484fdba48f01b2d8ef1b2786f5aa482fdaa4,
    0x9aeda1d9ae991d9ae1b9d98ed99d98e9a9d98e5b9d92e9b1e90edb1e96e1b9f94e5b9f,
    0x90fd99c68bcd8094f1a1c90f9a1c9cedb1d9ce591d9ce1a9d6cb4d8092f1b1c90f5b1c,
    0x64c4d8094f591c92f991c9ee9b1d9ee5a1d9ee199d9d25b2d9cf5b1f96f199c66c0d80,
    0x992dbac98fdb9e96f9b9c94fdb9c6eb0d809f21b2d9ef1b1f96f5a9c6ab8d8092fda9c,
    0xa2e991ba2e1b9ba0f969ba0f579ba0f189ba0ed99ba0e9a9ba0e5b9b9b29bac9af9b9e,
    0xa4e591ba4e1a9b6c94f806c9ce809301b1a9105b1aa2fd69ba2f581ba2f171ba2eda1b,
    0x66a8e80910d99a689508068a4e809501a1a9109a1aa4fd79ba4f981ba4f161ba4edb1b,
    0xa6fd89ba6f971ba6f561ba6e9b1ba6e5a1ba6e199ba525b27a505b1f6695100970199a,
    0xa721b27a701b1f6a950009705a9a6aa0e80930da9a649518064ace80950591a930991a,
    0xa8e571ba8e189ba329ba6a309b9ea12dba6a10db9e6e94f009709b9a950db9a6e98e80,
    0x5ea8f80911579a609d08060a4f80990181a911181aa8fd99ba8f9a1ba8e961ba8f5b1b,
    0xa929a25a909a1d9d0169a5aa51005aa9080911969aa925b25a905b1d5e9d1009b0179a,
    0x990571a931171aaafda9baaf991baaed61baaf1b1baae581baae179ba92d9a5a90d99d,
    0x5aa1180931d69aab21b25ab01b1d629d0009b0589a62a0f80931589a5c9d1805cacf80,
    0x6e9ce009b11b9a9915b9a6e90f80ab2daa5ab0da9dab29925ab0991d9f0569a5aad000,
    0xacf591baced71bacf1a1bace981bace169b6eb4d00a331ba4a311b9ca135ba4a115b9c,
    0xad01a1d62a4f009d0989a6299080951989a58a518058ad080990961a951161aacfdb9b,
    0x6a91080ad2dba5ad0db9dad25925ad0591d9f0979a5eacf005e99180951d79aad21a25,
    0x991d99a66911806abcd00a531aa4a511a9ca139aa4a119a9c6aa4e009d11a9a9919a9a,
    0xad45badad35ba7ad15b9fa7319a4a71199c66c4d00a13d9a4a11d99c9f1199a66ace00,
    0x58a900058a11009b0d61a971561aaef9b9baef5a9baeed89baef199baee979baee569b,
    0x9f0d81a60a0f006099000971d81aaf219a5af0199d5ca8f009d0d71a5c99100971971a,
    0xa339924a31991c64a8e009d1591a9b1991a6491100af29ba5af09b9daf25aa5af05a9d,
    0x68b8d00a33da24a31da1c9f15a1a68a0e009b1da1a689100064c0d00a535924a51591c,
    0x6cb0d009f19b1a9d1db1a6c98e006c90f00af41badaf31ba7af11b9fa735a24a715a1c,
    0xab49b2cab39b26ab19b1ea94db2ca93db26a91db1ea739b24a719b1ca53db24a51db1c,
    0xb959b86b8e5b93b355b09b2e9b14b151b09b0edb14b75db88b6e1b95b559b88b4e5b95,
    0xbb55906bae9913bb68d80bb5db86bae1b93b96cd80b951986b8ed993b955a86b8e9a93,
    0xbce1a93bd64d806cb47846cb4882b34db07b2f1b12b149b07b0f5b12bb51a06baeda13,
    0x68bc882b54da07b4f1a12b145a07b0f9a12bd51b06bcedb13bd59906bce5913bd5da86,
    0xbd65b2dbd49b08bcf5b15b74d987b6f199266c078466c0882b141987b0fd99268bc784,
    0xb4f5912b345907b2f9912bf55b06bee9b13bf59a06bee5a13bf5d986bee1993bf60d80,
    0xbef1b15b749a87b6f5a926ab87846ab8882b341a87b2fda9264c478464c4882b549907,
    0xb941b89b8fdb94b745b87b6f9b92b541b87b4fdb926eb07846eb0882bf61b2dbf4db08,
    0xc151984c0ed991c155a84c0e9a91c159b84c0e5b91bb69bacbb45b89baf9b94b96dbac,
    0xc17d180c179080c174f80c145684c0f9691c149784c0f5791c14d884c0f1891c16ce80,
    0xc34d704c2f1711c370f80c351a04c2eda11c355904c2e9911c368e80c35db84c2e1b91,
    0xb33db05b301b10b139b05b105b10c37d000c379100c341684c2fd691c349804c2f5811,
    0xc4edb11c559904c4e5911c55da84c4e1a91c564e806c947886c94a826c9c7866c9c982,
    0xc57cf00c541784c4fd791c545804c4f9811c54d604c4f1611c575100c571080c551b04,
    0xb131985b10d990689478a6894b8268a478668a4982b53da05b501a10b135a05b109a10,
    0xc760e80c565b27c539b08c505b15669478d6694c02b73d985b70199066a878666a8982,
    0xc6f5611c778f00c775000c771180c755b04c6e9b11c759a04c6e5a11c75d984c6e1991,
    0x64ac982b539905b505910b335905b309910c741884c6fd891c745704c6f9711c749604,
    0x6a94b02b739a85b705a906aa07866aa0982b331a85b30da90649478c6494c8264ac786,
    0xb735b85b709b90b531b85b50db906e987866e98982c761b27c73db08c701b156a9478b,
    0xc969080c964f80c369ba6c335b89c309b94c16dba6c131b89c10db946e947896e94a02,
    0xc8f9a11c955604c8e9611c949b04c8f5b11c959704c8e5711c95d884c8e1891c96d100,
    0x60a478860a4a82b93d805b901810b12d805b111810c97ce00c941984c8fd991c945a04,
    0x5e9c78d5e9cc02bb3d785bb017905ea87885ea8a82b129785b115790609c78a609cb82,
    0xbd016905aa478d5aa4c025aa878a5aa8b82b125685b119690c965b25c939b06c905b13,
    0xcb69180cb60f80c98cd00c96d9a5c931986c90d993c969a25c935a06c909a13bd3d685,
    0xcb51604caed611cb78e00cb4db04caf1b11cb59804cae5811cb5d784cae1791cb6d000,
    0x5cac7885caca82b939705b905710b32d705b311710cb41a84cafda91cb45904caf9911,
    0x629c78b629cb02bb39885bb0589062a078862a0a82b329885b3158905c9c78c5c9cc82,
    0x5aac78b5aacb025aa078c5aa0c82b321685b31d690cb88d00cb61b25cb3db06cb01b13,
    0x6e907886e90a82cb6daa5cb31a86cb0da93cb69925cb35906cb09913bf39685bf05690,
    0xc311b92c175ba4c129b87c115b926e9c7876e9c902bb2db85bb11b90b929b85b915b90,
    0xcd74e00cd5d684cce1691cd6cf00cd65180cd610806eb47856eb4802c371ba4c32db87,
    0xcd41b84ccfdb91cd49904ccf5911cd51704cced711cd4da04ccf1a11cd55804cce9811,
    0xb519890cd84d0058a478c58a4c8258ac78a58acb82b935605b909610b52d605b511610,
    0xcd61a25cd3da06cd01a1362a478962a4a02bd35885bd09890629878a6298b82b525885,
    0xcd39906cd05913bf35785bf097905eac7895eaca025e9878c5e98c82b521785b51d790,
    0xbd2da85bd11a90b925a85b919a906a9078a6a90b82cd6dba5cd31b86cd0db93cd65925,
    0x6abc7856abc802c571aa4c52da87c511a92c179aa4c125a87c119a926aa47876aa4902,
    0xc121987c11d992bf2d985bf1199066ac78766ac902b921985b91d990669078c6690c82,
    0xcd85badcd75ba7cd29b88cd15b95c7719a4c72d987c71199266c478566c4802c17d9a4,
    0xcf4d984cef1991cf55784cee9791cf59684cee5691cf70e00cf68f00cf65000cf61100,
    0xbb0d610b729605b715610cf80d00cf45b84cef9b91cf49a84cef5a91cf51884ceed891,
    0xbd0d7105c9878d5c98c02b725705b71971058a878b58a8b0258a078d58a0c02bb31605,
    0x609878b6098b02b721805b71d810cf619a5cf3d986cf019935ca87895ca8a02bd31705,
    0xcf69ba5cf35b86cf09b93cf65aa5cf39a86cf05a93bf31805bf0d81060a078960a0a02,
    0xc325907c31991264a878764a8902bd29905bd15910bb25905bb19910649078d6490c02,
    0xbb21a05bb1da10689078b6890b0264c078564c0802c575924c529907c515912c379924,
    0xc715a1268b878568b8802c37da24c321a07c31da12bf29a05bf15a1068a078768a0902,
    0x6c987876c989026c907896c90a02cf81badcf71ba7cf2db88cf11b95c775a24c729a07,
    0xc719b12c57db24c521b07c51db126cb07856cb0802bf25b05bf19b10bd21b05bd1db10,
    0xcb89b2ccb79b26cb25b09cb19b14c98db2cc97db26c921b09c91db14c779b24c725b07,
    0xd0f578fd14d882d0f188fd16d280d151982d0ed98fd155a82d0e9a8fd159b82d0e5b8f,
    0xd10548fd139482d10158fd13d582d17d580d179480d175380d145682d0f968fd149782,
    0xd199b80d195a80d191980d18d880d189780d185680d11128fd12d282d10938fd135382,
    0xd34d702d2f170fd371380d351a02d2eda0fd355902d2e990fd369280d35db82d2e1b8f,
    0xd339502d30140fd33d402d381680d37d400d379500d341682d2fd68fd349802d2f580f,
    0xd39db80d395900d391a00d38d700d389800d31528fd329282d30d38fd331382d30550f,
    0x6c6c9886c6ca866c748886c74a846c7c8866c7c984b31db03b321b0eb119b03b125b0e,
    0xd571480d551b02d4edb0fd559902d4e590fd55da82d4e1a8fd565280931db019119b01,
    0xd585800d581780d57d300d541782d4fd78fd545802d4f980fd54d602d4f160fd575500,
    0xd591b00d58d600d51928fd525282d50d48fd531482d50950fd535502d50130fd53d302,
    0x687488a6874b8468848866884984b51da03b521a0eb115a03b129a0ed59da80d599900,
    0xb71d983b72198e66888866688984b111983b12d98e951da019115a01686c98a686cb86,
    0xd761280d565b1fd525b15d519b08971d9819111981666c98d666cc06667488d6674c04,
    0xd6f560fd779300d775400d771580d755b02d6e9b0fd759a02d6e5a0fd75d982d6e198f,
    0xd70530fd739302d789600d785700d781880d741882d6fd88fd745702d6f970fd749602,
    0xb32990ed79d980d799a00d795b00d71d28fd721282d70d58fd731582d70940fd735402,
    0x9315901646c98c646cc86647488c6474c84648c886648c984b519903b52590eb315903,
    0x6a6cb066a7488b6a74b04b719a83b725a8e6a808866a80984b311a83b32da8e9519901,
    0xb511b83b52db8e6e788866e78984d761b1fd721b15d71db089719a819311a816a6c98b,
    0xd12db94d111b899715b819511b816e6c9896e6ca066e748896e74a04b715b83b729b8e,
    0xd8e570fd95d882d8e188fd96d500d969480d965380d369b9ed329b94d315b89d16db9e,
    0xd97d200d941982d8fd98fd945a02d8f9a0fd955602d8e960fd949b02d8f5b0fd959702,
    0xd925382d91548fd929482d91150fd92d502d90120fd93d202d989b00d985a00d981980,
    0x60848886084a84b91d803b92180eb10d803b13180ed99d880d999700d995600d91938f,
    0x5e888885e88a84b109783b13578e991d801910d801606ca8a606cb88607c88a607cb84,
    0xd925b13d919b069b1d78191097815e6ca8d5e6cc085e7c88d5e7cc04bb1d783bb2178e,
    0x5a6cc0abd1d683bd2168e5a8488d5a84c045a8888a5a88b84b105683b13968ed965b1d,
    0xd9acd00d96d99dd92d993d911986d969a1dd929a13d915a069d1d68191056815a6cb8d,
    0xdaf1b0fdb59802dae580fdb5d782dae178fdb6d400db69580db61380a94cd8178ecd81,
    0xdb85900db81a80db41a82dafda8fdb45902daf990fdb51602daed60fdb79200db4db02,
    0xdb1d38fdb21382db1558fdb29582db1140fdb2d402db0520fdb39202db91600db8db00,
    0x5c7c88c5c7cc845c8c8885c8ca84b919703b92570eb30d703b33170edb9d780db99800,
    0xbb19883bb2588e62808886280a84b309883b33588e9919701930d7015c6ca8c5c6cc88,
    0xdba8d00db61b1ddb21b13db1db069b198819309881626ca8b626cb08627c88b627cb04,
    0xbf19683bf2568e5a8c88b5a8cb045a8088c5a80c84b301683b33d68eab48d817ae8d81,
    0xdb6da9ddb2da93db11a86db6991ddb29913db159065a6cc8b5a6cb0c9f196819301681,
    0x9b0db819909b816e7c8876e7c904bb0db83bb31b8eb909b83b935b8e6e708886e70a84,
    0x6eb48836eb4704d371b9cd331b92d30db87d175b9cd135b92d109b876e6ca876e6c908,
    0xdcf1a0fdd55802dce980fdd75200dd5d682dce168fdd6d300dd65580dd614806eb4d81,
    0xdd8da00dd89900dd81b80dd41b82dcfdb8fdd49902dcf590fdd51702dced70fdd4da02,
    0xdd1d48fdd21482dd1958fdd25582dd1130fdd2d302dd0920fdd35202dd95800dd91700,
    0x586cc8a588488c5884c84588c88a588cb84b915603b92960eb50d603b53160edd9d680,
    0x627888a6278b84b505883b53988ead44d817ce4d81dda4d009915601950d601586cb8c,
    0xdd21a13dd1da06626cb89626ca0a9d15881950588162848896284a04bd15883bd2988e,
    0x9501781bf15783bf2978e5e8c8895e8ca045e7888c5e78c84b501783b53d78edd61a1d,
    0x6a70b84dd6db9ddd2db93dd11b86dd6591ddd25913dd199065e6cc895e6ca0c9f15781,
    0x6a6c90a9d0da819905a816a848876a84904bd0da83bd31a8eb905a83b939a8e6a7088a,
    0x6abcd816abc8836abc704d571a9cd531a92d50da87d179a9cd139a92d105a876a6cb87,
    0x9f0d9819901981bf0d983bf3198e668c887668c904b901983b93d98e667088c6670c84,
    0xd731992d70d98766c4d8166c488366c4704d17d99cd13d992d101987666cc87666c90c,
    0xdee568fdf71200df69300df65400df61500dda5baddd75b9fdd35b95dd09b88d77199c,
    0xdef9b8fdf49a82def5a8fdf51882deed88fdf4d982def198fdf55782dee978fdf59682,
    0xdf29302df0d20fdf31202df99680df95780df91880df8d980df89a80df85b80df45b82,
    0xb709603b73560eaf40d817ee0d81dfa0d00df1d50fdf21502df1940fdf25402df1530f,
    0x586cc0b586cb0d9b116019709601588888b5888b04588088d5880c04bb11603bb2d60e,
    0x9d1170197057015c888895c88a04bd11703bd2d70e5c7888d5c78c04b705703b73970e,
    0x6080a04607888b6078b04b701803b73d80edf6199ddf21993df1d9865c6cc095c6ca0d,
    0xdf65a9ddf25a93df19a86606cb09606ca0b9f118019701801bf11803bf2d80e6080889,
    0x6488904bd09903bd3590ebb05903bb3990e647088d6470c04df69b9ddf29b93df15b86,
    0xd535912d509907d37991cd339912d305907646cc07646c90d9d099019b059016488887,
    0x68808876880904bb01a03bb3da0e687088b6870b0464c0d8164c088364c0704d57591c,
    0x68b8704d37da1cd33da12d301a07686cb07686c90b9f09a019b01a01bf09a03bf35a0e,
    0x6c70a04dfa1baddf71b9fdf31b95df0db88d775a1cd735a12d709a0768b8d8168b8883,
    0x6c6c9099f05b019d01b01bf05b03bf39b0ebd01b03bd3db0e6c788876c789046c70889,
    0xd779b1cd739b12d705b07d57db1cd53db12d501b076cb0d816cb08836cb07046c6ca07,
    0xe169780e165680dba9b2cdb79b1edb39b14db05b09d9adb2cd97db1ed93db14d901b09,
    0xe105b0fe139b02e159402e0e540fe15d582e0e158fe179b00e175a00e171980e16d800,
    0xe12d802e0f120fe14d202e18d200e10d98fe131982e109a0fe135a02e155302e0e930f,
    0xb0fd503b14150ee19d580e199400e195300e11968fe125682e11578fe129782e11180f,
    0xa11d50190fd5015474a8a5474b88547c98a547cb8654849885484a86c11d503c12150e,
    0x5274a8d5274c08527c98d527cc06c31d483c32148e52889885288a86b0f9483b14548e,
    0x4e84c064e8898a4e88b86b0f5383b14938ee165b1be125b11e119b04a31d48190f9481,
    0xe169a1be129a11e115a04a51d38190f53814e74b8d4e74c0ac51d383c52138e4e8498d,
    0x4a88a8a4a88b88b15128eb0ed283a93ce8180ece81e1ace00e16d99be12d991e111984,
    0xe131811e10d804c91d283c92128ea91d28190ed2814a7cb8d4a7cc0a4a84a8d4a84c08,
    0xa53cf8180f4f81e1b4f00e17969be139691e105684e17579be135791e109784e17181b,
    0xe371a80e36d700e369880e361680a13d10180fd101e1bd180a33d08180f9081e1b9000,
    0xe2ed30fe389200e301b0fe33db02e359502e2e550fe35d482e2e148fe37db00e375900,
    0xe31170fe32d702e2f520fe349202e391300e30da8fe331a82e30990fe335902e351302,
    0xc119403c12540eb2fd403b34140ee39d480e399500e31d68fe321682e31588fe329882,
    0xb2f9583b34558ea11940192fd4015074a8c5074c88507c98c507cc86508c988508ca86,
    0xa31958192f95815674a8b5674b08567c98b567cb06c319583c32558e56809885680a86,
    0x4e8098c4e80c86b2f1383b34d38eab38e8182e8e81e3a8e00e361b1be321b11e31db04,
    0xe329911e3159044e74c8b4e74b0ca71938192f1381c719383c72538e4e8c98b4e8cb06,
    0x4a80c88b35528eb2e9283a738f8182f0f81e3b0f00e36da9be32da91e311a84e36991b,
    0xe30d704cb19283cb2528e4a7cc8b4a7cb0cab1928192e92814a8ca8b4a8cb084a80a8c,
    0x82f9181e3b9100e37d69be33d691e301684e37589be335891e309884e37171be331711,
    0xc145b8ec0f9b83a2fdb81a0f9b816e689886e68a86a13900182fd001e3bd080a339181,
    0xd2fdb85d185b9ad145b90d0f9b856e74a856e748086e7c9856e7c806c341b8ec2fdb83,
    0xe565880e5617806e94f816e94a836e947086e9ce816e9c9836e9c706d381b9ad341b90,
    0xe53da02e555502e4e950fe585200e55d382e4e138fe57da00e579900e571b80e56d600,
    0xe545202e595500e591400e50db8fe531b82e50590fe539902e551402e4ed40fe501a0f,
    0xb4fd303b54130ee59d380e51d78fe521782e51988fe525882e51160fe52d602e4f920f,
    0xa11530194fd3014c74b8c4c74c8a4c8498c4c84c864c8c98a4c8cb86c115303c12930e,
    0x5684a06c515583c52958e567898a5678b86b4f5583b54958ead34e8184e4e81e5a4e00,
    0xb4f1483b54d48ee561a1be521a11e51da045674b895674a0aa51558194f55815684989,
    0x5274c895274a0ca71548194f1481c715483c72948e528c989528ca06527898c5278c86,
    0xe5b5100a73508184f1081e5b1000e56db9be52db91e511b84e56591be525911e519904,
    0x4a8cb894a8ca0aad1528194e52814a78b8c4a78c8ab55928eb4e5283a53518184f5181,
    0xe57989be539891e505884e57161be531611e50d604cd15283cd2928e4a84c894a84a0c,
    0xa4fda81a0f5a816a6898a6a68b86a134f0184fcf01e5bcf80e57d79be53d791e501784,
    0xd149a90d0f5a856a74b856a7480a6a849856a84806c541a8ec4fda83c149a8ec0f5a83,
    0x6a950816a94b836a9470a6aa4e816aa49836aa4706d581a9ad541a90d4fda85d189a9a,
    0xc74198ec6fd983668c985668c806c14d98ec0f1983a6fd981a0f1981666898c6668c86,
    0xd741990d6fd98566ace8166ac98366ac706d18d99ad14d990d0f19856674c85667480c,
    0xe765700e761800e5a5ba7e585b9fe545b95e4f9b8866951816694c83669470cd78199a,
    0xe73d982e755482e6e948fe759382e6e538fe781200e77d980e779a80e775b80e769600,
    0xe799380e795480e791580e709b8fe735b82e705a8fe739a82e751582e6ed58fe70198f,
    0x86e0e81e7a0e00e71d80fe721802e71970fe725702e71560fe729602e6fd20fe741202,
    0x96f93014c8898b4c88b064c8098d4c80c06c311303c32d30eb6f9303b74530eaf30e81,
    0x5088a06c511403c52d40e507898d5078c06b6f5403b74940e4c74c0b4c74b0da311301,
    0xb6f1503b74d50ee76199be721991e71d9845074c095074a0da51140196f54015088989,
    0x5474b095474a0ba71150196f1501c711503c72d50e54809895480a06547898b5478b06,
    0xe7b5080a73110186f1101e7b1180e769b9be729b91e715b84e765a9be725a91e719a84,
    0x4a78b0daf1128196e1281b75d28eb6e1283a330f0186f8f01e7b8f80a53100186f5001,
    0xe77561be735611e709604cf11283cf2d28e4a88b094a88a0b4a80c094a80a0d4a78c0b,
    0xa4f9901a2f5901646898d6468c06e77d81be73d811e701804e77971be739711e705704,
    0xd349910d2f59056474c05647480d64889856488806c54590ec4f9903c34990ec2f5903,
    0x64951016494c03649470d64a8e8164a898364a8706d58591ad545910d4f9905d38991a,
    0xc745a0ec6f9a0368809856880806c34da0ec2f1a03a6f9a01a2f1a01686898b6868b06,
    0xd745a10d6f9a0568a0e8168a098368a0706d38da1ad34da10d2f1a056874b05687480b,
    0x6c689896c68a06e7a1ba7e781b9fe741b95e6fdb8868950016894b03689470bd785a1a,
    0x6c74a056c74809c749b0ec6f5b03c54db0ec4f1b036c789856c78806a6f5b01a4f1b01,
    0x6c94709d789b1ad749b10d6f5b05d58db1ad54db10d4f1b056c98e816c989836c98706,
    0xe3a9b26e389b1ee349b14e2f5b09e1adb26e18db1ee14db14e0f1b096c94f016c94a03,
    0xe989400e985300e95d282e8e128fe97d800e979700e975600e969b80e965a80e961980,
    0xe929b82e90570fe939702e8f540fe949402e90180fe93d802e8f150fe94d502e98d500,
    0xe99d280e91d98fe921982e919a8fe925a82e90960fe935602e8f930fe945302e915b8f,
    0x487cb8c487cc8a4884a8c4884c88488ca8a488cb88c10d203c13120eb8fd203b94120e,
    0x88ed181e9ad100ab2d08188e9081e9a9000ad2cf8188e4f81e9a4f00a10d20198fd201,
    0x5684908c90d583c93158ea90d58198ed5815670a8a5670b88b95158eb8ed583a92d181,
    0x5270a8c5270c88b95548eb8e9483e96181be921811e91d804567cb87567c90a5684a87,
    0xe925711e919704527cc87527c90ccb0d483cb3148e528ca87528c908ab0d48198e9481,
    0xad0d38198e53814e70b8c4e70c8ab95938eb8e5383e975b9be935b91e909b84e96571b,
    0xe905a84e96961be929611e915604cd0d383cd3138e4e84c874e8490c4e8cb874e8c90a,
    0x6268a8a6268b88a12ce0188fce01e9bce80e97d99be93d991e901984e979a9be939a91,
    0x627cb85627c80a6284a856284808c94188ec8fd883c15188ec0ed883a8fd881a0ed881,
    0x629c70a62a4f8162a4a8362a4708d98189ad941890d8fd885d19189ad151890d0ed885,
    0x5e8ca855e8c808c15578ec0e9783aafd781a0e97815e68a8c5e68c88629d081629cb83,
    0x5eacf815eaca835eac708d19579ad155790d0e97855e7cc855e7c80ccb4178ecafd783,
    0xe9a5ba5e985b9de945b93e8f9b865e9d1815e9cc835e9c70cdb8179adb41790dafd785,
    0x5a84c855a8480c5a8cb855a8c80ac15968ec0e5683acfd681a0e56815a68b8c5a68c8a,
    0x5aa4c835aa470c5aad0815aacb835aac70ad19969ad159690d0e5685cd4168eccfd683,
    0xe94d993e8f1986e9a9aa5e989a9de949a93e8f5a86dd8169add41690dcfd6855aa5181,
    0xeb79880eb71600eb6db80eb65900eb61a00992cd01890cd01e9ccd80e9ad9a5e98d99d,
    0xeb0178feb3d782eaf148feb4d482eb8d480eb89580eb59282eae528feb81300eb7d780,
    0xeb31602eafd30feb41302eb99280eb11b8feb2db82eb0588feb39882eaf558feb49582,
    0xbaf9203bb4520eaf28f818ae0f81eba0f00eb1da0feb21a02eb1990feb25902eb0d60f,
    0x487cc0b487cb0da3092019af92014888a8b4888b084880a8d4880c08c309203c33520e,
    0x5070a8d5070c08bb5140ebaed403a9290018aed001ebad080ab291018ae9101eba9180,
    0xeb21791eb1d784507cc07507c90d5088a875088908c909403c93540ea9094019aed401,
    0xcb3550e5480a875480908ab095019ae95015470a8b5470b08bb5550ebae9503eb6179b,
    0xebb8e80eb71b9beb31b91eb0db84eb6589beb25891eb19884547cb07547c90bcb09503,
    0x4e80c074e8090d4e70c0b4e70b0daf093819ae1381bb5d38ebae1383a328e018af8e01,
    0xeb7991beb39911eb05904eb6d61beb2d611eb11604cf09383cf3538e4e88b074e8890b,
    0xc8f9703c35170ec2ed703a8f9701a2ed7015c68a8d5c68c08eb7da1beb3da11eb01a04,
    0xd945710d8f9705d39171ad351710d2ed7055c7cc055c7c80d5c88a855c88808c94570e,
    0xa2e98016068a8b6068b085c9d1015c9cc035c9c70d5ca8f815ca8a835ca8708d98571a,
    0xd2e9805607cb05607c80bcb4580ecaf98036080a856080808c35580ec2e9803aaf9801,
    0x609cb03609c70bdb8581adb45810daf980560a0f8160a0a8360a0708d39581ad355810,
    0xaef9681a2e16819b28d018b08d01ebc8d80eba1ba5eb81b9deb41b93eafdb86609d001,
    0xcf4568ecef96835a88b055a8880b5a80c055a8080dc35d68ec2e16835a68c0b5a68b0d,
    0xdef96855aa90015aa8b035aa870b5aa11015aa0c035aa070dd39d69ad35d690d2e1685,
    0xebada25eb8da1deb4da13eaf1a06eba9925eb8991deb49913eaf5906df8569adf45690,
    0xcb51b0ecaedb03c955b0ec8e9b036c70a856c708086c68a876c68908aaedb01a8e9b01,
    0xdb51b10daedb05d995b1ad955b10d8e9b056c90f816c90a836c907086c7c9056c7c807,
    0xe351b12e2edb07e1b5b24e195b1ce155b12e0e9b076c9ce016c9c9036c9c707db91b1a,
    0xed75880ed71700ed6da80ed69900ed61b006cb4d016cb48036cb4705e3b1b24e391b1c,
    0xed0168fed3d682ecf138fed4d382ed8d380ed55282ece928fed85580ed81400ed7d680,
    0xed31702ecfd40fed41402ed11a8fed2da82ed0988fed35882ecf958fed45582ed95280,
    0x8ce5101eda5180af250818ce1081eda1000ed1db0fed21b02ed1590fed29902ed0d70f,
    0x4888a0aa5052019cf52014878b8d4878c0ac505203c53920ebcf5203bd4920ead25101,
    0x4c70b8d4c70c0abd5130ebced303a924f018cecf01edacf804884c094884a0d4888b89,
    0xed21691ed1d6844c84c074c8490d4c88b874c8890ac905303c93930ea9053019ced301,
    0x5470b895470a0aad055019ce5501bd5950ebce5503a524e018cf4e01edb4e80ed6169b,
    0xed0da84ed6989bed29891ed158845484a075484909cd05503cd3950e5478b87547890a,
    0x5278c07527890d5270c095270a0daf054819ce1481bd5d48ebce1483ed71a9bed31a91,
    0xed7591bed35911ed09904ed6d71bed2d711ed11704cf05483cf3948e5288a075288909,
    0xc8f5603c55160ec4ed603a8f5601a4ed6015868b8d5868c0aed7db1bed3db11ed01b04,
    0xd949610d8f5605d59161ad551610d4ed6055884c05588480d5888b85588880ac94960e,
    0x9d24d018d04d01edc4d8058a510158a4c0358a470d58a908158a8b8358a870ad98961a,
    0xcd4980eccf58036078b85607880ac55980ec4e58036068b896068a0aacf5801a4e5801,
    0xdd49810dcf580560990816098b83609870ad59981ad559810d4e58056084a056084809,
    0xaef5781a4e1781eda1aa5ed81a9ded41a93ecfda8660a4f0160a4a0360a4709dd8981a,
    0xcf4978ecef57835e88a055e888095e78c055e7880dc55d78ec4e17835e68c095e68a0d,
    0xdef57855ea8f015ea8a035ea87095e991015e98c035e9870dd59d79ad55d790d4e1785,
    0xedadb25ed8db1ded4db13ecf1b06eda5925ed8591ded45913ecf9906df8979adf49790,
    0xcd51a0ecceda03c959a0ec8e5a036870b85687080a6868b87686890aaceda01a8e5a01,
    0xdd51a10dceda05d999a1ad959a10d8e5a0568910816890b83689070a68849056884807,
    0xe551a12e4eda07e1b9a24e199a1ce159a12e0e5a0768a4e0168a490368a4707dd91a1a,
    0x667080d6668c07666890daeed981a8e198168bcd0168bc80368bc705e5b1a24e591a1c,
    0x66911016690c03669070dcf5198eceed98366889056688807c95d98ec8e19836670c05,
    0xe0e1987df9199adf51990deed98566a8e0166a890366a8707d99d99ad95d990d8e1985,
    0xe7b19a4e79199ce751992e6ed98766c0d0166c080366c0705e1bd9a4e19d99ce15d992,
    0xef75780ef71800ef6d980ef69a00ef65b00edc5b2dedb5b27ed95b1fed55b15ece9b08,
    0xef39682eef538fef49382ef91280ef51282eeed28fef89380ef85480ef81500ef79680,
    0xef31802eefd50fef41502ef1198fef2d982ef0978fef35782eef948fef45482ef0568f,
    0x8ee5001efa5080af211818ee1181efa1100ef19b0fef25b02ef15a0fef29a02ef0d80f,
    0xa7012019ef1201c701203c73d20ebef1203bf4d20eab20f018ee8f01efa8f80ad21001,
    0xbee9303a720e018ef0e01efb0e80488cb09488ca0b4880c894880a0c4878c8b4878b0c,
    0x4c8c90b4c80c874c8090ccb01303cb3d30e4c70c8b4c70b0cab013019ee9301bf5530e,
    0x5070c895070a0cad014019ee5401bf5940ebee5403ef6569bef25691ef196844c8cb07,
    0xef0d984ef6979bef29791ef15784508ca07508c909cd01403cd3d40e5078c87507890c,
    0x5678b07567890b5670b095670a0baf015819ee1581bf5d58ebee1583ef7199bef31991,
    0xef75a1bef35a11ef09a04ef6d81bef2d811ef11804cf01583cf3d58e5680a075680909,
    0x5868c8b5868b0caaf1601a6e96019f20d018f00d01efc0d80ef79b1bef39b11ef05b04,
    0xd755610d6e9605588cb05588c80b5880c85588080ccb4d60ecaf1603c75560ec6e9603,
    0x58ad00158acb0358ac70b58a118158a0c8358a070cdb8d61adb4d610daf1605d79561a,
    0xcd4d70eccf17035c78c855c7880cc75970ec6e57035c68c895c68a0cacf1701a6e5701,
    0xdd4d710dcf17055c991815c98c835c9870cd79971ad759710d6e57055c8ca055c8c809,
    0xaef1881a6e1881efa19a5ef8199def41993eefd9865cacf015caca035cac709dd8d71a,
    0xcf4d88ecef18836280a0562808096278b05627880bc75d88ec6e18836268b096268a0b,
    0xdef188562a0f0162a0a0362a070962990016298b03629870bd79d89ad75d890d6e1885,
    0xefa9b25ef89b1def49b13eef5b06efa5a25ef85a1def45a13eef9a06df8d89adf4d890,
    0xcd5590ecce9903cb5990ecae59036470c85647080c6468c87646890cace9901aae5901,
    0xdd55910dce9905db9991adb59910dae590564911816490c83649070c648c905648c807,
    0xe555912e4e9907e3b9924e39991ce359912e2e590764ace0164ac90364ac707dd9591a,
    0x6a7080b6a68b076a6890baee9a81aae1a8164c4d0164c480364c4705e5b5924e59591c,
    0x6a910016a90b036a9070bcf55a8ecee9a836a809056a80807cb5da8ecae1a836a70b05,
    0xe2e1a87df95a9adf55a90dee9a856aa0e016aa09036aa0707db9da9adb5da90dae1a85,
    0xe7b5aa4e795a9ce755a92e6e9a876ab8d016ab88036ab8705e3bdaa4e39da9ce35da92,
    0x6e708096e68a076e68909aee5b81ace1b81efc1b2defb1b27ef91b1fef51b15eeedb08,
    0x6e90f016e90a036e90709cf59b8ecee5b83cd5db8ecce1b836e789056e788076e70a05,
    0x6eb0705df99b9adf59b90dee5b85dd9db9add5db90dce1b856e98e016e989036e98707,
    0xe7b9ba4e799b9ce759b92e6e5b87e5bdba4e59db9ce55db92e4e1b876eb0d016eb0803,
    0xebc9bacebb9ba6eb99b9eeb59b94eae5b89e9cdbace9bdba6e99db9ee95db94e8e1b89
  ]

/-- The `3150` quadruples, `28` bits each, ordered by their closure. -/
@[expose] public def blkPack : Nat :=
  blkWords.foldr (fun v acc => acc * 2 ^ 280 + v) 0

/-- Entry `i` of the table. -/
@[expose] public def blkCode (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight blkPack (Nat.mul 28 i)) 268435455

@[expose] public def blkA (i : Nat) : Nat := Nat.mod (blkCode i) 128

@[expose] public def blkB (i : Nat) : Nat := Nat.mod (Nat.div (blkCode i) 128) 128

@[expose] public def blkC (i : Nat) : Nat := Nat.mod (Nat.div (blkCode i) 16384) 128

@[expose] public def blkD (i : Nat) : Nat := Nat.mod (Nat.div (blkCode i) 2097152) 128

/-- The `i`-th block: the closure of the `i`-th quadruple. -/
@[expose] public def blkAt (i : Nat) : Bitset :=
  quadSet (blkA i) (blkB i) (blkC i) (blkD i)

/-- The certificate of one entry: the quadruple is four classes, pairwise
orthogonal, whose closure holds twelve classes, and its closure is below the
next entry's. The final entry has no successor, so the order clause is skipped
there rather than reaching past the end of the table. -/
@[expose] public def blkEntryOK (i : Nat) : Bool :=
  quadOK (blkA i) (blkB i) (blkC i) (blkD i)
    && (decide (i + 1 = 3150)
      || decide (Bitset.toNat (blkAt i) < Bitset.toNat (blkAt (i + 1))))

/-- Entries `[lo, lo + len)`, checked. -/
@[expose] public def blkRange (lo : Nat) : Nat → Bool
  | 0 => true
  | (n + 1) => blkRange lo n && blkEntryOK (lo + n)

/-- Entries `[0, n)`, checked. -/
@[expose] public def blkUpTo : Nat → Bool
  | 0 => true
  | (n + 1) => blkUpTo n && blkEntryOK n

/-- Windows compose, exactly as they do for the count. -/
public theorem blkUpTo_add (lo : Nat) : ∀ len : Nat,
    blkUpTo (lo + len) = (blkUpTo lo && blkRange lo len) := by
  intro len
  induction len with
  | zero =>
    show blkUpTo lo = (blkUpTo lo && true)
    rw [Bool.and_true]
  | succ n ih =>
    show (blkUpTo (lo + n) && blkEntryOK (lo + n))
      = (blkUpTo lo && (blkRange lo n && blkEntryOK (lo + n)))
    rw [ih, Bool.and_assoc]

public theorem blkUpTo_true : ∀ n : Nat, blkUpTo n = true →
    ∀ i : Nat, i < n → blkEntryOK i = true := by
  intro n
  induction n with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    intro h i hi
    have h2 : (blkUpTo m && blkEntryOK m) = true := h
    rw [Bool.and_eq_true] at h2
    rcases Nat.lt_or_ge i m with hlt | hge
    · exact ih h2.1 i hlt
    · have hEq : i = m := by omega
      rw [hEq]
      exact h2.2

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin0 : blkRange 0 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin1 : blkRange 150 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin2 : blkRange 300 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin3 : blkRange 450 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin4 : blkRange 600 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin5 : blkRange 750 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin6 : blkRange 900 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin7 : blkRange 1050 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin8 : blkRange 1200 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin9 : blkRange 1350 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin10 : blkRange 1500 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin11 : blkRange 1650 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin12 : blkRange 1800 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin13 : blkRange 1950 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin14 : blkRange 2100 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin15 : blkRange 2250 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin16 : blkRange 2400 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin17 : blkRange 2550 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin18 : blkRange 2700 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin19 : blkRange 2850 150 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem blkWin20 : blkRange 3000 150 = true := by decide +kernel

/-- Every entry of the table is certified. -/
public theorem blkAll : blkUpTo 3150 = true := by
  have s0 : blkUpTo 0 = true := rfl
  have h0 := blkUpTo_add 0 150
  rw [s0, blkWin0] at h0
  have s1 : blkUpTo 150 = true := h0
  have h1 := blkUpTo_add 150 150
  rw [s1, blkWin1] at h1
  have s2 : blkUpTo 300 = true := h1
  have h2 := blkUpTo_add 300 150
  rw [s2, blkWin2] at h2
  have s3 : blkUpTo 450 = true := h2
  have h3 := blkUpTo_add 450 150
  rw [s3, blkWin3] at h3
  have s4 : blkUpTo 600 = true := h3
  have h4 := blkUpTo_add 600 150
  rw [s4, blkWin4] at h4
  have s5 : blkUpTo 750 = true := h4
  have h5 := blkUpTo_add 750 150
  rw [s5, blkWin5] at h5
  have s6 : blkUpTo 900 = true := h5
  have h6 := blkUpTo_add 900 150
  rw [s6, blkWin6] at h6
  have s7 : blkUpTo 1050 = true := h6
  have h7 := blkUpTo_add 1050 150
  rw [s7, blkWin7] at h7
  have s8 : blkUpTo 1200 = true := h7
  have h8 := blkUpTo_add 1200 150
  rw [s8, blkWin8] at h8
  have s9 : blkUpTo 1350 = true := h8
  have h9 := blkUpTo_add 1350 150
  rw [s9, blkWin9] at h9
  have s10 : blkUpTo 1500 = true := h9
  have h10 := blkUpTo_add 1500 150
  rw [s10, blkWin10] at h10
  have s11 : blkUpTo 1650 = true := h10
  have h11 := blkUpTo_add 1650 150
  rw [s11, blkWin11] at h11
  have s12 : blkUpTo 1800 = true := h11
  have h12 := blkUpTo_add 1800 150
  rw [s12, blkWin12] at h12
  have s13 : blkUpTo 1950 = true := h12
  have h13 := blkUpTo_add 1950 150
  rw [s13, blkWin13] at h13
  have s14 : blkUpTo 2100 = true := h13
  have h14 := blkUpTo_add 2100 150
  rw [s14, blkWin14] at h14
  have s15 : blkUpTo 2250 = true := h14
  have h15 := blkUpTo_add 2250 150
  rw [s15, blkWin15] at h15
  have s16 : blkUpTo 2400 = true := h15
  have h16 := blkUpTo_add 2400 150
  rw [s16, blkWin16] at h16
  have s17 : blkUpTo 2550 = true := h16
  have h17 := blkUpTo_add 2550 150
  rw [s17, blkWin17] at h17
  have s18 : blkUpTo 2700 = true := h17
  have h18 := blkUpTo_add 2700 150
  rw [s18, blkWin18] at h18
  have s19 : blkUpTo 2850 = true := h18
  have h19 := blkUpTo_add 2850 150
  rw [s19, blkWin19] at h19
  have s20 : blkUpTo 3000 = true := h19
  have h20 := blkUpTo_add 3000 150
  rw [s20, blkWin20] at h20
  have s21 : blkUpTo 3150 = true := h20
  exact s21

public theorem blkEntry_true {i : Nat} (hi : i < 3150) : blkEntryOK i = true :=
  blkUpTo_true 3150 blkAll i hi

/-- Every entry of the table is a `D16` block. -/
public theorem blkD16 {i : Nat} (hi : i < 3150) : D16 (blkAt i) := by
  have h := blkEntry_true hi
  simp only [blkEntryOK, Bool.and_eq_true] at h
  exact block_of_quadOK h.1

public theorem blkMono {i : Nat} (hi : i + 1 < 3150) :
    Bitset.toNat (blkAt i) < Bitset.toNat (blkAt (i + 1)) := by
  have h := blkEntry_true (by omega : i < 3150)
  simp only [blkEntryOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h.2 with hbe | hlt
  · exact absurd hbe (by omega)
  · exact hlt

/-- The table is strictly increasing, so its entries are pairwise distinct. -/
public theorem blkLt : ∀ i j : Nat, i < j → j < 3150 →
    Bitset.toNat (blkAt i) < Bitset.toNat (blkAt j) := by
  intro i j
  induction j with
  | zero => intro h; exact absurd h (Nat.not_lt_zero i)
  | succ m ih =>
    intro hij hm
    rcases Nat.lt_or_ge i m with hlt | hge
    · exact Nat.lt_trans (ih hlt (by omega)) (blkMono (by omega))
    · have hEq : i = m := by omega
      rw [hEq]
      exact blkMono (by omega)

public theorem blkInj {i j : Nat} (hi : i < 3150) (hj : j < 3150) (hne : i ≠ j) :
    blkAt i ≠ blkAt j := by
  intro heq
  rcases Nat.lt_or_ge i j with h | h
  · have hlt := blkLt i j h hj
    rw [heq] at hlt
    exact absurd hlt (Nat.lt_irrefl _)
  · have hji : j < i := by omega
    have hlt := blkLt j i hji hi
    rw [heq] at hlt
    exact absurd hlt (Nat.lt_irrefl _)

/-- `3150` blocks, exhibited and pairwise distinct.

This is the *exhibition* half of `T22` and is deliberately not labelled `T22`:
`T22` is `|Blk| = 3150`, which also needs completeness -- that no `D16` block
is missing from the table -- and completeness is not proved in this module.
See the note at the head of the module. -/
public theorem blkExhibit :
    (∀ i : Nat, i < 3150 → D16 (blkAt i))
      ∧ (∀ i j : Nat, i < 3150 → j < 3150 → i ≠ j → blkAt i ≠ blkAt j) :=
  ⟨fun _ hi => blkD16 hi, fun _ _ hi hj hne => blkInj hi hj hne⟩

/-! ## The table holds every closure

The table exhibits `3150` blocks; this section proves that no closure escapes
it: whenever `a < b < c < d` are pairwise orthogonal classes whose closure
holds twelve classes, that closure is an entry of the table. This is the
completeness of the *enumeration*. It is not the completeness of the census,
which would also have to know that every `D16` block arises as such a closure,
but it is the half of that obligation which is a computation.

The sweep is four nested bounded conjunctions rather than the mask walk of the
count, and that is deliberate: `allRange_true` instantiates a passing sweep at
any concrete quadruple with no lemma about `bitsOf`, `above` or `orthMask` in
between, so the extraction below is four applications of one lemma. A mask walk
would be faster per node and would cost a proof that the walk reaches every
quadruple, which is exactly the obligation this section exists to discharge.
Orthogonality
is tested as "bit not set in the adjacency row", which is exactly `adjBit`, and
`adjBit_eq` already ties that to `adjN` and `dot_of_adjN` to the inner product.
The rows are threaded down the levels: `adjRow` cuts a row out of a
`14400`-bit table, and one extraction per node instead of three per leaf is the
difference between minutes and hours.

Membership in the table is decided by a binary search, and the search is *not*
proved correct: `inTable` verifies the entry the search returns, so a wrong
answer fails the check rather than passing a false claim. -/

/-- Binary search over the table, which is ordered by the closure numeral.
Thirteen halvings cover `3150` entries. -/
@[expose] public def blkFind (t : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | (f + 1), lo, hi =>
      (fun mid => if Nat.blt (Bitset.toNat (blkAt mid)) t then blkFind t f (mid + 1) hi
        else blkFind t f lo mid) (Nat.div (lo + hi) 2)

@[expose] public def blkIdx (a b c d : Nat) : Nat :=
  blkFind (Bitset.toNat (quadSet a b c d)) 13 0 3150

/-- The closure of `(a,b,c,d)` is the table entry the search returned. -/
@[expose] public def inTable (a b c d : Nat) : Bool :=
  decide (blkIdx a b c d < 3150)
    && decide (Bitset.toNat (blkAt (blkIdx a b c d)) = Bitset.toNat (quadSet a b c d))

/-- What an orthogonal quadruple owes the table: either its closure is not a
block's worth of classes, or it is an entry. -/
@[expose] public def covered (a b c d : Nat) : Bool :=
  !decide (Bitset.card (quadSet a b c d) = 12) || inTable a b c d

/-- A bounded conjunction over `[lo, lo + n)`. `allLt` would start at `0` and
the sweep's three inner levels all start above their parent, so a quarter of
the nodes below are the ones that can matter: `1250750` iterations against
`5004000`. -/
@[expose] public def allRange (f : Nat → Bool) (lo : Nat) : Nat → Bool
  | 0 => true
  | (n + 1) => allRange f lo n && f (lo + n)

public theorem allRange_true : ∀ (f : Nat → Bool) (lo n : Nat),
    allRange f lo n = true → ∀ k : Nat, k < n → f (lo + k) = true := by
  intro f lo n
  induction n with
  | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ m ih =>
    intro h k hk
    have h2 : (allRange f lo m && f (lo + m)) = true := h
    rw [Bool.and_eq_true] at h2
    rcases Nat.lt_or_ge k m with hlt | hge
    · exact ih h2.1 k hlt
    · have hEq : k = m := by omega
      rw [hEq]
      exact h2.2

/-- Bit `j` of a threaded row. This is `adjBit i j` with the row extraction
lifted out, which is what makes the sweep affordable. -/
@[expose] public def rowBit (r j : Nat) : Bool := Nat.beq (Nat.mod (Nat.shiftRight r j) 2) 1

/-- The `d` level: `d` above `c`, and in none of the three adjacency rows. -/
@[expose] public def sweepD (ra rb rc a b c : Nat) : Bool :=
  allRange (fun d => rowBit ra d || rowBit rb d || rowBit rc d || covered a b c d)
    (c + 1) (119 - c)

/-- The `c` level. -/
@[expose] public def sweepC (ra rb a b : Nat) : Bool :=
  allRange (fun c => rowBit ra c || rowBit rb c || sweepD ra rb (adjRow c) a b c)
    (b + 1) (119 - b)

/-- The `b` level. -/
@[expose] public def sweepB (ra a : Nat) : Bool :=
  allRange (fun b => rowBit ra b || sweepC ra (adjRow b) a b) (a + 1) (119 - a)

/-- Every quadruple whose least member is `a`. -/
@[expose] public def sweepA (a : Nat) : Bool := sweepB (adjRow a) a

@[expose] public def sweepRange (lo : Nat) : Nat → Bool
  | 0 => true
  | (n + 1) => sweepRange lo n && sweepA (lo + n)

@[expose] public def sweepUpTo : Nat → Bool
  | 0 => true
  | (n + 1) => sweepUpTo n && sweepA n

public theorem sweepUpTo_add (lo : Nat) : ∀ len : Nat,
    sweepUpTo (lo + len) = (sweepUpTo lo && sweepRange lo len) := by
  intro len
  induction len with
  | zero =>
    show sweepUpTo lo = (sweepUpTo lo && true)
    rw [Bool.and_true]
  | succ n ih =>
    show (sweepUpTo (lo + n) && sweepA (lo + n))
      = (sweepUpTo lo && (sweepRange lo n && sweepA (lo + n)))
    rw [ih, Bool.and_assoc]

public theorem sweepUpTo_true : ∀ n : Nat, sweepUpTo n = true →
    ∀ i : Nat, i < n → sweepA i = true := by
  intro n
  induction n with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    intro h i hi
    have h2 : (sweepUpTo m && sweepA m) = true := h
    rw [Bool.and_eq_true] at h2
    rcases Nat.lt_or_ge i m with hlt | hge
    · exact ih h2.1 i hlt
    · have hEq : i = m := by omega
      rw [hEq]
      exact h2.2

/-- Orthogonal classes are not adjacent, so the row bit is clear. `adjBit_eq`
carries the packed table to `adjN` and `dot_of_adjN` carries `adjN` to the
inner product; this is the only place the sweep's guard meets the geometry. -/
public theorem rowBit_zero {i j : Nat} (hi : i < 120) (hj : j < 120)
    (h : dot (repN i) (repN j) = 0) : rowBit (adjRow i) j = false := by
  have hb : adjBit i j = adjN i j := adjBit_eq hi hj
  have h0 : adjN i j = 0 := by
    rcases Nat.lt_or_ge (adjN i j) 1 with hlt | hge
    · omega
    · have h1 : adjN i j = 1 := Nat.le_antisymm (adjN_le_one i j) hge
      rcases dot_of_adjN h1 with hh | hh
      · rw [h] at hh; exact absurd hh (by decide)
      · rw [h] at hh; exact absurd hh (by decide)
  show Nat.beq (adjBit i j) 1 = false
  rw [hb, h0]
  rfl


set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin0 : sweepRange 0 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin1 : sweepRange 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin2 : sweepRange 4 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin3 : sweepRange 6 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin4 : sweepRange 8 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin5 : sweepRange 10 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin6 : sweepRange 12 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin7 : sweepRange 14 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin8 : sweepRange 17 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin9 : sweepRange 20 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin10 : sweepRange 23 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin11 : sweepRange 26 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin12 : sweepRange 30 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin13 : sweepRange 34 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin14 : sweepRange 38 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin15 : sweepRange 43 6 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin16 : sweepRange 49 7 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin17 : sweepRange 56 6 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin18 : sweepRange 62 6 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin19 : sweepRange 68 9 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin20 : sweepRange 77 17 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
public theorem sweepWin21 : sweepRange 94 26 = true := by decide +kernel

/-- The sweep, window by window. The windows are cut for equal work, not
equal width: the quadruples above a class thin out sharply as the class
rises, so `[94, 120)` is one window and `[0, 2)` is another. -/
public theorem sweepAll : sweepUpTo 120 = true := by
  have s0 : sweepUpTo 0 = true := rfl
  have h0 := sweepUpTo_add 0 2
  rw [s0, sweepWin0] at h0
  have s1 : sweepUpTo 2 = true := h0
  have h1 := sweepUpTo_add 2 2
  rw [s1, sweepWin1] at h1
  have s2 : sweepUpTo 4 = true := h1
  have h2 := sweepUpTo_add 4 2
  rw [s2, sweepWin2] at h2
  have s3 : sweepUpTo 6 = true := h2
  have h3 := sweepUpTo_add 6 2
  rw [s3, sweepWin3] at h3
  have s4 : sweepUpTo 8 = true := h3
  have h4 := sweepUpTo_add 8 2
  rw [s4, sweepWin4] at h4
  have s5 : sweepUpTo 10 = true := h4
  have h5 := sweepUpTo_add 10 2
  rw [s5, sweepWin5] at h5
  have s6 : sweepUpTo 12 = true := h5
  have h6 := sweepUpTo_add 12 2
  rw [s6, sweepWin6] at h6
  have s7 : sweepUpTo 14 = true := h6
  have h7 := sweepUpTo_add 14 3
  rw [s7, sweepWin7] at h7
  have s8 : sweepUpTo 17 = true := h7
  have h8 := sweepUpTo_add 17 3
  rw [s8, sweepWin8] at h8
  have s9 : sweepUpTo 20 = true := h8
  have h9 := sweepUpTo_add 20 3
  rw [s9, sweepWin9] at h9
  have s10 : sweepUpTo 23 = true := h9
  have h10 := sweepUpTo_add 23 3
  rw [s10, sweepWin10] at h10
  have s11 : sweepUpTo 26 = true := h10
  have h11 := sweepUpTo_add 26 4
  rw [s11, sweepWin11] at h11
  have s12 : sweepUpTo 30 = true := h11
  have h12 := sweepUpTo_add 30 4
  rw [s12, sweepWin12] at h12
  have s13 : sweepUpTo 34 = true := h12
  have h13 := sweepUpTo_add 34 4
  rw [s13, sweepWin13] at h13
  have s14 : sweepUpTo 38 = true := h13
  have h14 := sweepUpTo_add 38 5
  rw [s14, sweepWin14] at h14
  have s15 : sweepUpTo 43 = true := h14
  have h15 := sweepUpTo_add 43 6
  rw [s15, sweepWin15] at h15
  have s16 : sweepUpTo 49 = true := h15
  have h16 := sweepUpTo_add 49 7
  rw [s16, sweepWin16] at h16
  have s17 : sweepUpTo 56 = true := h16
  have h17 := sweepUpTo_add 56 6
  rw [s17, sweepWin17] at h17
  have s18 : sweepUpTo 62 = true := h17
  have h18 := sweepUpTo_add 62 6
  rw [s18, sweepWin18] at h18
  have s19 : sweepUpTo 68 = true := h18
  have h19 := sweepUpTo_add 68 9
  rw [s19, sweepWin19] at h19
  have s20 : sweepUpTo 77 = true := h19
  have h20 := sweepUpTo_add 77 17
  rw [s20, sweepWin20] at h20
  have s21 : sweepUpTo 94 = true := h20
  have h21 := sweepUpTo_add 94 26
  rw [s21, sweepWin21] at h21
  have s22 : sweepUpTo 120 = true := h21
  exact s22

/-- Every orthogonal quadruple whose closure holds twelve classes closes to an
entry of the table.

The quadruple is asked to be increasing because the sweep enumerates increasing
quadruples. That is the enumeration's convention rather than a restriction on
the geometry -- `quadSet` is symmetric in its four arguments, since `Nat.lor`
and `Nat.land` are -- but that symmetry is not needed here and is not proved,
so a caller holding an unordered quadruple has to sort it first. -/
public theorem quad_in_table {a b c d : Nat}
    (ha : a < 120) (hb : b < 120) (hc : c < 120) (hd : d < 120)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (oab : dot (repN a) (repN b) = 0) (oac : dot (repN a) (repN c) = 0)
    (oad : dot (repN a) (repN d) = 0) (obc : dot (repN b) (repN c) = 0)
    (obd : dot (repN b) (repN d) = 0) (ocd : dot (repN c) (repN d) = 0)
    (hcard : Bitset.card (quadSet a b c d) = 12) :
    ∃ i : Nat, i < 3150 ∧ blkAt i = quadSet a b c d := by
  have hA : allRange (fun b => rowBit (adjRow a) b
      || sweepC (adjRow a) (adjRow b) a b) (a + 1) (119 - a) = true :=
    sweepUpTo_true 120 sweepAll a ha
  have hB0 := allRange_true _ _ _ hA (b - a - 1) (by omega)
  rw [show a + 1 + (b - a - 1) = b from by omega, rowBit_zero ha hb oab] at hB0
  simp only [Bool.false_or] at hB0
  have hB : allRange (fun c => rowBit (adjRow a) c || rowBit (adjRow b) c
      || sweepD (adjRow a) (adjRow b) (adjRow c) a b c) (b + 1) (119 - b) = true := hB0
  have hC0 := allRange_true _ _ _ hB (c - b - 1) (by omega)
  rw [show b + 1 + (c - b - 1) = c from by omega, rowBit_zero ha hc oac,
    rowBit_zero hb hc obc] at hC0
  simp only [Bool.false_or] at hC0
  have hC : allRange (fun d => rowBit (adjRow a) d || rowBit (adjRow b) d
      || rowBit (adjRow c) d || covered a b c d) (c + 1) (119 - c) = true := hC0
  have hD := allRange_true _ _ _ hC (d - c - 1) (by omega)
  rw [show c + 1 + (d - c - 1) = d from by omega, rowBit_zero ha hd oad,
    rowBit_zero hb hd obd, rowBit_zero hc hd ocd] at hD
  simp only [Bool.false_or] at hD
  simp only [covered, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hD
  rcases hD with h | h
  · exact absurd hcard h
  · simp only [inTable, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨blkIdx a b c d, h.1, h.2⟩


/-! ## What completeness still needs

`T22` is `|Blk| = 3150`. Three things would prove it and two of them are above:
the table exhibits `3150` distinct blocks, and `quad_in_table` shows the table
holds every closure. The third is the implication neither supplies -- that a
`D16` block is a closure at all, that is, that its twelve classes contain four
pairwise orthogonal ones -- and it is not an enumeration: there are
`C(120,4) = 8214570` four-element class subsets and a span test on a general
quadruple is a linear solve.

The route short enough for this kernel runs through the Gram type of the
block's own basis. `D16` hands over four independent roots `b_0..b_3` whose
classes lie in `B`. Their Gram matrix has diagonal `8` and off-diagonal in
`{0,+-4}`: `+-8` is excluded because it forces `b_j = +-b_i`. So the type is
one of `3^6 = 729` matrices, of which `393` are positive definite, and for a
class `v` of `B` the vector `d_v := (<rep v, b_i>)` lies in `{0,+-4,+-8}^4`,
one of `625` candidates. Positive definiteness makes `v |-> d_v` injective, and
`v` lies in the span exactly when `d^T G^-1 d = 8`, which the adjugate turns
into the integer identity `d^T adj(G) d = 8 det(G)`: no rational matrix inverse
is needed anywhere.

The finite check that closes it, computed outside the kernel and recorded here
so that the next pass does not have to rediscover it. Over all `393`
positive-definite types the number of admissible `d` never exceeds `24`, with
distribution `{10:12, 12:12, 14:64, 20:200, 24:105}`. Every one of the `105`
types reaching `24` contains four pairwise orthogonal admissible vectors, and
more than that: *every* admissible vector of such a type extends to an
orthogonal quadruple, which is what would let the quadruple be chosen through
the block's least class and so match the ordering `quad_in_table` asks for.
Each of the `336` types that is not positive definite carries an integer `z` in
`{-2..2}^4`, `z != 0`, with `z^T G z <= 0`, and that contradicts the
independence of `b` through `dot_self_zero`. Since `|B| = 12` gives `24`
distinct admissible vectors, the count is forced to `24`, `B` is exactly the
classes of the span, and `mem_quadSet_iff_inSpan` turns that into
`B = quadSet q`.

Two obligations inside that route are not computations and are worth naming.
The pigeonhole from "`24` distinct admissible vectors" to "the admissible set
is exactly these" needs a counting lemma for the image of a `Bitset` under an
injection, which this repository does not have. And `quad_in_table` asks for an
increasing quadruple, so the four orthogonal classes the argument produces have
to be sorted, which needs the symmetry of `quadSet` in its four arguments --
true, since `Nat.lor` and `Nat.land` are commutative and associative, but not
proved above.

Nothing in this module is claimed on the strength of any of that, and no label
is carried by any of it.
-/

end UorAtlas.Census

end
