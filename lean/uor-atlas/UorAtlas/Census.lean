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

end UorAtlas.Census

end
