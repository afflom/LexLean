module
public import Init
public import UorAtlas.Prelude.Algebra
public import UorAtlas.Prelude.Linear
public import UorAtlas.Prelude.Bitset
public import UorAtlas.Prelude.Perm
public import UorAtlas.Roots
public import UorAtlas.Blocks
public import UorAtlas.Places
public import UorAtlas.Category

/-!
Sections 5, 6, 10 and 11 of `UOR-ATLAS-FORMAL-001`: the reflection generators
`D20`, the automorphism group `D21`, and the counting theorems that rest on
them.

## Why permutations are carried as packed tables

`D20` defines `s_a` by its action on root *vectors*: the class of `x` goes to
the class of `x - (<x,a>/4) a`. Evaluating that map once costs a dot product,
eight coordinate updates and a linear search of the `120` class words -- about
a thousand kernel reductions. `Aut` has `348364800` elements, and the
certificates below apply group elements tens of thousands of times, so the
vector form is unusable as a *computational* presentation.

`ap` and `pak` fix that. A permutation of `Fin 120` is packed into one `Nat`,
seven bits per slot, and `tperm` turns such a word into a `Perm 120` once the
word has been checked to describe a bijection. `D20_apply` is the bridge: the
permutation `D20 a` *is* the reflection of the document, evaluated. Nothing is
assumed -- `D20perm` is a table computed outside the kernel, and `D20lit_eq`
makes the kernel recompute it from `D19a`, `rep` and `D12` and compare.

`pak` is `Roots.pk` at base `128` written with shifts instead of powers, and
`pak_eq_pk` says so, so `pk_digit` supplies the round-trip lemma while the
kernel runs shifts.

## What the chain is used for twice

`autChain` counts `Aut`. The same machinery, run on four elements that fix the
witness AtlasInstance setwise, counts the group those four generate: five
levels, orbits `48, 3, 8, 2, 2`, product `4608`. That is only a *lower* half of
the gauge group until something rules out a fifth element, and `gauge_eq` is
that something: an element of `Aut` fixing `W_0` is identified level by level
against the base points of `autSpec`, because the image of a base point has the
same profile inside `W_0` as the base point -- the same membership, the same
adjacencies to the points already fixed, and the same counts of walks inside
`W_0` -- and those profiles pin it to the stored transversal. After the seventh
level the element fixes all seven base points, and `aut_fix_trivial` reads off
the bottom of `autChain` that it is the identity.

What that yields is `|Gauge(W_0)| = 4608` for the witness instance and nothing
about any other instance: carrying it to a second instance is transitivity of
`Aut` on `Atl`, which is the document's `T27` and is not proved anywhere in
this library. `T29` and `T49` are stated for *every* instance and are therefore
not claimed here; `gaugeOrderWitness` is the witness case under its own name.
The same gap is why `orbitAction` instantiates the nineteen theorems of
`UorAtlas.Category` over the `Aut`-orbit of `W_0` rather than over `Atl`.

## Why `-I` needs a sign and not a class

`V68b` has to distinguish `-I` from `I`, and nothing about classes can: both
act trivially on `K`. The fold of `signStep` carries one extra bit -- whether
the reflected representative is the representative of its image class or its
negative -- and running it along `(r_1 ... r_8)^15` on the eight simple roots
shows the word negates a basis. `T73` is not needed: a matrix that negates a
basis *is* `-I`.

## Why the arithmetic is spelled out

Every `Bool` that a certificate below reduces is written in `Nat.beq`,
`Nat.blt`, `Nat.mod`, `Nat.shiftRight` and `Nat.shiftLeft` rather than in `==`,
`<`, `%`, `>>>` and `decide`. The two are definitionally equal, and the proofs
use whichever reads better; but the kernel reduces what is written, and the
notation goes through `Decidable` and `BEq` instances whose unfolding costs
several kilobytes of retained term per step. At the scale of this module --
about a million elementary steps -- that is the difference between three
gigabytes and thirty. `allLt` and `pak` are `Nat.rec` for the same reason, and
the recursive `Bool`s below match on their argument rather than fold.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace UorAtlas.Group

open UorAtlas.Prelude
open UorAtlas.Prelude.Linear
open UorAtlas.Roots

/-! ## Permutations as packed words -/

/-- Slot `j` of a packed word: seven bits, so slots hold values below `128`. -/
@[expose] public def ap (t j : Nat) : Nat := Nat.mod (Nat.shiftRight t (Nat.mul 7 j)) 128

/-- Pack the first `m` values of `v`, seven bits each. -/
@[expose] public def pak (v : Nat → Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k ih => Nat.add (Nat.shiftLeft (v k) (Nat.mul 7 k)) ih) m

public theorem pak_succ (v : Nat → Nat) (m : Nat) :
    pak v (m + 1) = Nat.add (Nat.shiftLeft (v m) (Nat.mul 7 m)) (pak v m) := rfl

public theorem pak_eq_pk (v : Nat → Nat) : ∀ m, pak v m = pk 128 v m := by
  intro m
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [pak_succ]
    show (v k <<< (7 * k)) + pak v k = v k * 128 ^ k + pk 128 v k
    rw [ih, Nat.shiftLeft_eq]
    have h : (2 : Nat) ^ (7 * k) = 128 ^ k := by
      rw [Nat.pow_mul]
    rw [h]

public theorem ap_eq (t j : Nat) : ap t j = t / 128 ^ j % 128 := by
  show (t >>> (7 * j)) % 128 = t / 128 ^ j % 128
  rw [Nat.shiftRight_eq_div_pow]
  have h : (2 : Nat) ^ (7 * j) = 128 ^ j := by rw [Nat.pow_mul]
  rw [h]

/-- The round trip: a packed word reads back the values it was built from. -/
public theorem ap_pak (v : Nat → Nat) (m : Nat) (hv : ∀ k, k < m → v k < 128)
    (j : Nat) (hj : j < m) : ap (pak v m) j = v j := by
  rw [ap_eq, pak_eq_pk]
  exact pk_digit 128 (by decide) v m hv j hj

-- Unfolding `pak` is the kernel's job, not the elaborator's: `mulT` is a `pak`
-- of `120` slots, so a unifier that whnfs one produces a term with a hundred
-- and twenty branches, and a unifier that whnfs a `tabOK` of two of them
-- produces fourteen thousand. The kernel ignores this attribute, which is the
-- point --- `decide +kernel` still reduces `pak` all the way.
attribute [irreducible] pak

/-! ## Packed words as permutations

`tabOK f b` says that `f` and `b` are packed words of mutually inverse maps of
`Fin 120`. It is a `Bool`, so a permutation is certified by one
`decide +kernel`; `tperm` is total, falling back on the identity, so that lists
of permutations can be *computed* without carrying a proof per entry. -/

@[expose] public def tabOK (f b : Nat) : Bool :=
  allLt (fun i => Nat.blt (ap f i) 120 && Nat.blt (ap b i) 120
    && Nat.beq (ap b (ap f i)) i && Nat.beq (ap f (ap b i)) i) 120

public theorem tabOK_fwd {f b : Nat} (h : tabOK f b = true) {i : Nat} (hi : i < 120) :
    ap f i < 120 :=
  Nat.le_of_ble_eq_true (Bool.and_eq_true _ _ |>.mp
    (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp
      (allLt_true _ _ h i hi)).1).1).1

public theorem tabOK_bwd {f b : Nat} (h : tabOK f b = true) {i : Nat} (hi : i < 120) :
    ap b i < 120 :=
  Nat.le_of_ble_eq_true (Bool.and_eq_true _ _ |>.mp
    (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp
      (allLt_true _ _ h i hi)).1).1).2

public theorem tabOK_left {f b : Nat} (h : tabOK f b = true) {i : Nat} (hi : i < 120) :
    ap b (ap f i) = i :=
  Nat.eq_of_beq_eq_true (Bool.and_eq_true _ _ |>.mp
    (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ h i hi)).1).2

public theorem tabOK_right {f b : Nat} (h : tabOK f b = true) {i : Nat} (hi : i < 120) :
    ap f (ap b i) = i :=
  Nat.eq_of_beq_eq_true (Bool.and_eq_true _ _ |>.mp (allLt_true _ _ h i hi)).2

/-- The permutation a certified pair of packed words describes. -/
@[expose] public def tperm (f b : Nat) : Perm 120 :=
  if h : tabOK f b = true then
    { toFun := fun i => ⟨ap f i.val, tabOK_fwd h i.isLt⟩
      invFun := fun i => ⟨ap b i.val, tabOK_bwd h i.isLt⟩
      left_inv := fun i => Fin.eq_of_val_eq (tabOK_left h i.isLt)
      right_inv := fun i => Fin.eq_of_val_eq (tabOK_right h i.isLt) }
  else Perm.one 120

public theorem tperm_toFun {f b : Nat} (h : tabOK f b = true) (i : Fin 120) :
    ((tperm f b).toFun i).val = ap f i.val := by
  rw [tperm, dif_pos h]

public theorem tperm_invFun {f b : Nat} (h : tabOK f b = true) (i : Fin 120) :
    ((tperm f b).invFun i).val = ap b i.val := by
  rw [tperm, dif_pos h]

/-! ## `D20`: the reflection generators

In the 2x scaling every root has `<x,x> = 8`, so the reflection in `a` is
`x |-> x - (<x,a>/4) a`; the division is exact because `<x,a>` is a multiple of
`4` on `R`. `D20vec` is that map on vectors, `D20idx` is it on class indices,
and `D20` is the packed permutation. -/

/-- The reflection of `D20` on vectors. -/
@[expose] public def D20vec (a : Fin 8) (x : Vec 8 Int) : Vec 8 Int :=
  fun j => x j - (dot x (D19a a) / 4) * D19a a j

/-- The reflection of `D20` on class indices. -/
@[expose] public def D20idx (a : Fin 8) (i : Nat) : Nat := (D12 (D20vec a (repN i))).val

/-- The reflection of `D20` as a packed word. -/
@[expose] public def D20tab (a : Fin 8) : Nat := pak (D20idx a) 120

public theorem D20idx_lt (a : Fin 8) (i : Nat) : D20idx a i < 128 :=
  Nat.lt_trans (D12 (D20vec a (repN i))).isLt (by decide)

public theorem ap_D20tab (a : Fin 8) {i : Nat} (hi : i < 120) :
    ap (D20tab a) i = D20idx a i :=
  ap_pak _ 120 (fun k _ => D20idx_lt a k) i hi

/-- Packing a list of slot values, least significant slot first. -/
@[expose] public def tabOf : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.add x (Nat.shiftLeft (tabOf xs) 7)

/-- The eight reflections as tables of class indices, computed outside the
kernel. Reading them back rather than recomputing them is what keeps every
later certificate affordable: one slot of `D20tab` costs a class lookup, and a
`decide +kernel` that mentioned `D20tab` would pay for all `960` of them again.
`D20lit_eq` is the check that makes that sound --- the kernel recomputes the
tables from `D19a`, `rep` and `D12` and compares --- so nothing here is
assumed, only cached. -/
@[expose] public def D20perm : List (List Nat) :=
  [[0, 88, 2, 72, 4, 64, 6, 60, 8, 58, 10, 57, 56, 13, 71, 15, 79, 17, 83, 19, 85, 21, 86, 23,
    24, 87, 95, 27, 99, 29, 101, 31, 102, 33, 34, 103, 107, 37, 109, 39, 110, 41, 42, 111,
    113, 45, 114, 47, 48, 115, 116, 51, 52, 117, 54, 118, 12, 11, 9, 59, 7, 61, 62, 63, 5, 65,
    66, 67, 68, 69, 70, 14, 3, 73, 74, 75, 76, 77, 78, 16, 80, 81, 82, 18, 84, 20, 22, 25, 1,
    89, 90, 91, 92, 93, 94, 26, 96, 97, 98, 28, 100, 30, 32, 35, 104, 105, 106, 36, 108, 38,
    40, 43, 112, 44, 46, 49, 50, 53, 55, 119],
   [0, 1, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13,
    12, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46,
    47, 48, 49, 50, 51, 52, 53, 54, 55, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75,
    74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 88, 89, 90,
    91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110,
    111, 112, 113, 114, 115, 116, 117, 118, 119],
   [0, 1, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
    13, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46,
    47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68,
    69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 119, 118, 117,
    116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99,
    98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88],
   [2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 26, 27, 28, 29, 30, 31, 32, 33, 34,
    35, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46,
    47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68,
    69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 72, 73,
    74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 104, 105, 106, 107, 108, 109, 110,
    111, 112, 113, 114, 115, 116, 117, 118, 119],
   [0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 14, 15, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 36, 37, 38, 39, 40, 41, 42, 43, 28, 29, 30, 31, 32, 33, 34, 35, 44, 45, 46,
    47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 72, 73, 74, 75, 76,
    77, 78, 79, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90,
    91, 92, 93, 94, 95, 104, 105, 106, 107, 108, 109, 110, 111, 96, 97, 98, 99, 100, 101, 102,
    103, 112, 113, 114, 115, 116, 117, 118, 119],
   [0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 16, 17, 20, 21, 22, 23, 24,
    25, 28, 29, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 44, 45, 46, 47, 48, 49, 38, 39, 40,
    41, 42, 43, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 64, 65, 66, 67, 60, 61, 62, 63, 68,
    69, 70, 71, 72, 73, 74, 75, 80, 81, 82, 83, 76, 77, 78, 79, 84, 85, 86, 87, 88, 89, 90,
    91, 96, 97, 98, 99, 92, 93, 94, 95, 100, 101, 102, 103, 104, 105, 106, 107, 112, 113, 114,
    115, 108, 109, 110, 111, 116, 117, 118, 119],
   [0, 1, 2, 3, 4, 5, 8, 9, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 18, 19, 22, 23, 24,
    25, 26, 27, 30, 31, 28, 29, 32, 33, 34, 35, 38, 39, 36, 37, 40, 41, 42, 43, 44, 45, 50,
    51, 52, 53, 46, 47, 48, 49, 54, 55, 56, 57, 60, 61, 58, 59, 62, 63, 64, 65, 68, 69, 66,
    67, 70, 71, 72, 73, 76, 77, 74, 75, 78, 79, 80, 81, 84, 85, 82, 83, 86, 87, 88, 89, 92,
    93, 90, 91, 94, 95, 96, 97, 100, 101, 98, 99, 102, 103, 104, 105, 108, 109, 106, 107, 110,
    111, 112, 113, 116, 117, 114, 115, 118, 119],
   [0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 20, 21, 24,
    25, 26, 27, 28, 29, 32, 33, 30, 31, 34, 35, 36, 37, 40, 41, 38, 39, 42, 43, 46, 47, 44,
    45, 48, 49, 50, 51, 54, 55, 52, 53, 56, 58, 57, 59, 60, 62, 61, 63, 64, 66, 65, 67, 68,
    70, 69, 71, 72, 74, 73, 75, 76, 78, 77, 79, 80, 82, 81, 83, 84, 86, 85, 87, 88, 90, 89,
    91, 92, 94, 93, 95, 96, 98, 97, 99, 100, 102, 101, 103, 104, 106, 105, 107, 108, 110, 109,
    111, 112, 114, 113, 115, 116, 118, 117, 119]]

/-- The eight reflection tables as packed words. -/
@[expose] public def D20lit : List Nat := D20perm.map tabOf

set_option maxHeartbeats 1000000 in
/-- The tables of `D20perm` are the reflections of `D20`. -/
public theorem D20lit_eq : (List.finRange 8).map D20tab = D20lit := by decide +kernel

/-- Each reflection is a permutation of the `120` classes, and an involution:
one packed word serves as its own inverse. -/
public theorem D20litOK : D20lit.all (fun t => tabOK t t) = true := by decide +kernel

public theorem D20tab_mem (a : Fin 8) : D20tab a ∈ D20lit :=
  D20lit_eq ▸ List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩

public theorem D20tabOK (a : Fin 8) : tabOK (D20tab a) (D20tab a) = true :=
  List.all_eq_true.mp D20litOK _ (D20tab_mem a)

/-- `D20`. `s_a`, the reflection in the simple root `a`, as a permutation of
the `120` classes of `D12`. -/
@[expose] public def D20 (a : Fin 8) : Perm 120 := tperm (D20tab a) (D20tab a)

/-- `D20` *is* the reflection of the document: on the class of `x` it returns
the class of `x - (<x,a>/4) a`. -/
public theorem D20_apply (a : Fin 8) (i : K) : (D20 a).toFun i = D12 (D20vec a (rep i)) := by
  refine Fin.eq_of_val_eq ?_
  rw [D20, tperm_toFun (D20tabOK a), ap_D20tab a i.isLt]
  rfl

/-! ## Counting a group presented by generators

`Aut` has `348364800` elements, so `T28` cannot be a list. What it can be is a
*stabiliser chain*: a sequence of subgroups `G = G_0 >= G_1 >= ... >= G_7 = 1`
in which `G_{i+1}` is the stabiliser in `G_i` of a point `b_i`, together with a
transversal of `G_{i+1}` in `G_i` indexed by the orbit of `b_i`. Then
`|G_i| = |orbit_i| * |G_{i+1}|`, and the product of the orbit lengths is the
order.

The load-bearing half is that `G_{i+1}` really is the *whole* stabiliser, not
just some subgroup of it. That is Schreier's lemma, `schreier_key` below: if
`t` is a transversal of the orbit of `b` then the stabiliser of `b` in
`< gens >` is generated by the elements `t(s.y)^{-1} s t(y)`. Its proof is an
induction over the generation of an arbitrary group element, and it is what
turns a finite, checkable list of Schreier generators into a statement about
all `348364800` elements.

`HasOrder` is stated as the existence of a duplicate-free list of *exactly* the
generated subgroup. The list is never evaluated -- it is built by `flatMap` out
of the transversal and the list one level down -- but its length is computed
symbolically, and `Nodup` plus the membership equivalence is what makes that
length the order and not merely an upper bound.
-/

/-- `< gens >` has exactly `N` elements. -/
@[expose] public def HasOrder (gens : List (Perm 120)) (N : Nat) : Prop :=
  ∃ L : List (Perm 120), L.Nodup ∧ (∀ g : Perm 120, g ∈ L ↔ Perm.Gen gens g) ∧ L.length = N

/-- The trivial group: no generators, one element. -/
public theorem hasOrder_nil : HasOrder [] 1 := by
  refine ⟨[Perm.one 120], List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun g => ?_, rfl⟩
  constructor
  · intro hg
    exact (List.mem_singleton.mp hg) ▸ Perm.Gen.one
  · intro hg
    induction hg with
    | one => exact List.mem_singleton.mpr rfl
    | step _ hs _ => exact absurd hs (by simp)
    | stepInv _ hs _ => exact absurd hs (by simp)

/-- A `flatMap` of duplicate-free fibres over a duplicate-free index list, whose
fibres are pairwise disjoint, is duplicate-free. -/
public theorem nodup_flatMap {α : Type} {β : Type} (f : α → List β) :
    ∀ l : List α, l.Nodup → (∀ a ∈ l, (f a).Nodup) →
      (∀ a₁ ∈ l, ∀ a₂ ∈ l, ∀ c : β, c ∈ f a₁ → c ∈ f a₂ → a₁ = a₂) →
      (l.flatMap f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _ _; exact List.nodup_nil
  | cons a as ih =>
    intro hnd hf hd
    have hnd' := List.nodup_cons.mp hnd
    rw [List.flatMap_cons]
    refine List.nodup_append.mpr ⟨hf a (List.mem_cons_self ..), ?_, ?_⟩
    · exact ih hnd'.2 (fun x hx => hf x (List.mem_cons_of_mem _ hx))
        (fun x₁ h₁ x₂ h₂ c hc₁ hc₂ =>
          hd x₁ (List.mem_cons_of_mem _ h₁) x₂ (List.mem_cons_of_mem _ h₂) c hc₁ hc₂)
    · intro c hc d hd' he
      obtain ⟨x, hx, hdx⟩ := List.mem_flatMap.mp hd'
      exact hnd'.1 (hd a (List.mem_cons_self ..) x (List.mem_cons_of_mem _ hx) c hc
        (he ▸ hdx) ▸ hx)

/-! ### One level of the chain

`gens` generates `G`, `gens'` generates the subgroup that is to be the
stabiliser of `b`, `O` is the orbit of `b` and `t` the transversal. -/

variable {gens gens' : List (Perm 120)} {b : Fin 120} {O : List (Fin 120)}
  {t : Fin 120 → Perm 120}

/-- A closed set of points is carried into itself by the whole group. -/
public theorem gen_maps (hOc : ∀ y ∈ O, ∀ s ∈ gens, s.toFun y ∈ O ∧ s.invFun y ∈ O)
    {g : Perm 120} (hg : Perm.Gen gens g) : ∀ y ∈ O, g.toFun y ∈ O := by
  induction hg with
  | one => intro y hy; exact hy
  | @step p s _ hs ih => intro y hy; exact ih _ (hOc y hy s hs).1
  | @stepInv p s _ hs ih => intro y hy; exact ih _ (hOc y hy s hs).2

/-- The subgroup generated by elements of `G` lies in `G`. -/
public theorem gen_sub (hsub : ∀ s ∈ gens', Perm.Gen gens s)
    {g : Perm 120} (hg : Perm.Gen gens' g) : Perm.Gen gens g := by
  induction hg with
  | one => exact Perm.Gen.one
  | step _ hs ih => exact Perm.Gen.comp_mem ih (hsub _ hs)
  | stepInv _ hs ih => exact Perm.Gen.comp_mem ih (Perm.Gen.inv_mem (hsub _ hs))

/-- The subgroup generated by elements fixing `b` fixes `b`. -/
public theorem gen_fixes (hfix : ∀ s ∈ gens', s.toFun b = b)
    {g : Perm 120} (hg : Perm.Gen gens' g) : g.toFun b = b := by
  induction hg with
  | one => rfl
  | @step p s _ hs ih =>
    show p.toFun (s.toFun b) = b
    rw [hfix _ hs, ih]
  | @stepInv p s _ hs ih =>
    show p.toFun (s.invFun b) = b
    have h : s.invFun b = b := by
      have hc := congrArg s.invFun (hfix _ hs)
      rw [s.left_inv] at hc
      exact hc.symm
    rw [h, ih]

/-- **Schreier's lemma**, in the form the induction proves: for every `g` in
`< gens >` and every `y` in the orbit, `t(g.y)^{-1} g t(y)` lies in the group
generated by the Schreier generators. -/
public theorem schreier_key
    (hOc : ∀ y ∈ O, ∀ s ∈ gens, s.toFun y ∈ O ∧ s.invFun y ∈ O)
    (hsch : ∀ y ∈ O, ∀ s ∈ gens,
      Perm.Gen gens' ((t (s.toFun y)).inv.comp (s.comp (t y))))
    {g : Perm 120} (hg : Perm.Gen gens g) :
    ∀ y ∈ O, Perm.Gen gens' ((t (g.toFun y)).inv.comp (g.comp (t y))) := by
  induction hg with
  | one =>
    intro y _
    have h : (t ((Perm.one 120).toFun y)).inv.comp ((Perm.one 120).comp (t y))
        = Perm.one 120 := Perm.inv_comp (t y)
    rw [h]
    exact Perm.Gen.one
  | @step p s _ hs ih =>
    intro y hy
    have hy' : s.toFun y ∈ O := (hOc y hy s hs).1
    have e : (t ((p.comp s).toFun y)).inv.comp ((p.comp s).comp (t y))
        = ((t (p.toFun (s.toFun y))).inv.comp (p.comp (t (s.toFun y)))).comp
            ((t (s.toFun y)).inv.comp (s.comp (t y))) :=
      Perm.ext fun i => by
        show (t (p.toFun (s.toFun y))).invFun (p.toFun (s.toFun ((t y).toFun i)))
          = (t (p.toFun (s.toFun y))).invFun (p.toFun ((t (s.toFun y)).toFun
              ((t (s.toFun y)).invFun (s.toFun ((t y).toFun i)))))
        rw [(t (s.toFun y)).right_inv]
    rw [e]
    exact Perm.Gen.comp_mem (ih _ hy') (hsch y hy s hs)
  | @stepInv p s _ hs ih =>
    intro y hy
    have hy' : s.invFun y ∈ O := (hOc y hy s hs).2
    have hry : s.toFun (s.invFun y) = y := s.right_inv y
    have hstep : Perm.Gen gens' ((t (s.invFun y)).inv.comp (s.inv.comp (t y))) := by
      have h0 := Perm.Gen.inv_mem (hsch (s.invFun y) hy' s hs)
      rwa [hry] at h0
    have e : (t ((p.comp s.inv).toFun y)).inv.comp ((p.comp s.inv).comp (t y))
        = ((t (p.toFun (s.invFun y))).inv.comp (p.comp (t (s.invFun y)))).comp
            ((t (s.invFun y)).inv.comp (s.inv.comp (t y))) :=
      Perm.ext fun i => by
        show (t (p.toFun (s.invFun y))).invFun (p.toFun (s.invFun ((t y).toFun i)))
          = (t (p.toFun (s.invFun y))).invFun (p.toFun ((t (s.invFun y)).toFun
              ((t (s.invFun y)).invFun (s.invFun ((t y).toFun i)))))
        rw [(t (s.invFun y)).right_inv]
    rw [e]
    exact Perm.Gen.comp_mem (ih _ hy') hstep

/-- The stabiliser of `b` in `< gens >` is exactly `< gens' >`. -/
public theorem stab_eq
    (hb : b ∈ O) (htb : t b = Perm.one 120)
    (hOc : ∀ y ∈ O, ∀ s ∈ gens, s.toFun y ∈ O ∧ s.invFun y ∈ O)
    (hsch : ∀ y ∈ O, ∀ s ∈ gens,
      Perm.Gen gens' ((t (s.toFun y)).inv.comp (s.comp (t y))))
    {g : Perm 120} (hg : Perm.Gen gens g) (hgb : g.toFun b = b) :
    Perm.Gen gens' g := by
  have h := schreier_key hOc hsch hg b hb
  rw [hgb, htb] at h
  have e : (Perm.one 120).inv.comp (g.comp (Perm.one 120)) = g := rfl
  rwa [e] at h

/-- **One level of the stabiliser chain.** `|G| = |orbit| * |stabiliser|`, with
the stabiliser identified as `< gens' >` by Schreier's lemma. -/
public theorem hasOrder_step
    (hb : b ∈ O) (hnd : O.Nodup) (htb : t b = Perm.one 120)
    (hti : ∀ y ∈ O, Perm.Gen gens (t y) ∧ (t y).toFun b = y)
    (hOc : ∀ y ∈ O, ∀ s ∈ gens, s.toFun y ∈ O ∧ s.invFun y ∈ O)
    (hsub : ∀ s ∈ gens', Perm.Gen gens s ∧ s.toFun b = b)
    (hsch : ∀ y ∈ O, ∀ s ∈ gens,
      Perm.Gen gens' ((t (s.toFun y)).inv.comp (s.comp (t y))))
    {N' : Nat} (h' : HasOrder gens' N') : HasOrder gens (O.length * N') := by
  obtain ⟨L', hL'nd, hL'mem, hL'len⟩ := h'
  have hsub1 : ∀ s ∈ gens', Perm.Gen gens s := fun s hs => (hsub s hs).1
  have hsub2 : ∀ s ∈ gens', s.toFun b = b := fun s hs => (hsub s hs).2
  have hfix : ∀ h : Perm 120, h ∈ L' → h.toFun b = b := fun h hh =>
    gen_fixes hsub2 ((hL'mem h).mp hh)
  refine ⟨O.flatMap (fun y => L'.map (fun h => (t y).comp h)), ?_, ?_, ?_⟩
  · refine nodup_flatMap _ O hnd (fun y _ => ?_) (fun y₁ h₁ y₂ h₂ c hc₁ hc₂ => ?_)
    · exact List.Pairwise.map _ (fun x z hxz he => hxz (Perm.comp_left_cancel he)) hL'nd
    · obtain ⟨u₁, hu₁, he₁⟩ := List.mem_map.mp hc₁
      obtain ⟨u₂, hu₂, he₂⟩ := List.mem_map.mp hc₂
      have k₁ : c.toFun b = y₁ := by
        rw [← he₁]
        show (t y₁).toFun (u₁.toFun b) = y₁
        rw [hfix u₁ hu₁]
        exact (hti y₁ h₁).2
      have k₂ : c.toFun b = y₂ := by
        rw [← he₂]
        show (t y₂).toFun (u₂.toFun b) = y₂
        rw [hfix u₂ hu₂]
        exact (hti y₂ h₂).2
      rw [← k₁, ← k₂]
  · intro g
    constructor
    · intro hg
      obtain ⟨y, hy, hgy⟩ := List.mem_flatMap.mp hg
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hgy
      exact Perm.Gen.comp_mem (hti y hy).1 (gen_sub hsub1 ((hL'mem h).mp hh))
    · intro hg
      have hy : g.toFun b ∈ O := gen_maps hOc hg b hb
      have htg : Perm.Gen gens ((t (g.toFun b)).inv.comp g) :=
        Perm.Gen.comp_mem (Perm.Gen.inv_mem (hti _ hy).1) hg
      have hfx : ((t (g.toFun b)).inv.comp g).toFun b = b := by
        show (t (g.toFun b)).invFun (g.toFun b) = b
        have hc := congrArg (t (g.toFun b)).invFun (hti _ hy).2
        rw [(t (g.toFun b)).left_inv] at hc
        exact hc.symm
      have hmem : Perm.Gen gens' ((t (g.toFun b)).inv.comp g) :=
        stab_eq hb htb hOc hsch htg hfx
      refine List.mem_flatMap.mpr ⟨g.toFun b, hy, List.mem_map.mpr
        ⟨(t (g.toFun b)).inv.comp g, (hL'mem _).mpr hmem, ?_⟩⟩
      show (t (g.toFun b)).comp ((t (g.toFun b)).inv.comp g) = g
      rw [← Perm.comp_assoc, Perm.comp_inv, Perm.one_comp]
  · rw [List.length_flatMap, List.map_congr_left (fun y _ => List.length_map ..), hL'len]
    exact ListAux.sum_map_const N'

/-- The membership test one level of the chain provides: an element lies in
`< gens >` exactly when it moves `b` inside the orbit and the coset
representative divides it back into the stabiliser. -/
public theorem gen_iff_step
    (hb : b ∈ O) (htb : t b = Perm.one 120)
    (hti : ∀ y ∈ O, Perm.Gen gens (t y) ∧ (t y).toFun b = y)
    (hOc : ∀ y ∈ O, ∀ s ∈ gens, s.toFun y ∈ O ∧ s.invFun y ∈ O)
    (hsub : ∀ s ∈ gens', Perm.Gen gens s ∧ s.toFun b = b)
    (hsch : ∀ y ∈ O, ∀ s ∈ gens,
      Perm.Gen gens' ((t (s.toFun y)).inv.comp (s.comp (t y))))
    (g : Perm 120) :
    Perm.Gen gens g ↔
      (g.toFun b ∈ O ∧ Perm.Gen gens' ((t (g.toFun b)).inv.comp g)) := by
  constructor
  · intro hg
    have hy : g.toFun b ∈ O := gen_maps hOc hg b hb
    refine ⟨hy, ?_⟩
    have htg : Perm.Gen gens ((t (g.toFun b)).inv.comp g) :=
      Perm.Gen.comp_mem (Perm.Gen.inv_mem (hti _ hy).1) hg
    have hfx : ((t (g.toFun b)).inv.comp g).toFun b = b := by
      show (t (g.toFun b)).invFun (g.toFun b) = b
      have hc := congrArg (t (g.toFun b)).invFun (hti _ hy).2
      rw [(t (g.toFun b)).left_inv] at hc
      exact hc.symm
    exact stab_eq hb htb hOc hsch htg hfx
  · rintro ⟨hy, hmem⟩
    have e : g = (t (g.toFun b)).comp ((t (g.toFun b)).inv.comp g) := by
      show g = (t (g.toFun b)).comp ((t (g.toFun b)).inv.comp g)
      rw [← Perm.comp_assoc, Perm.comp_inv, Perm.one_comp]
    rw [e]
    exact Perm.Gen.comp_mem (hti _ hy).1
      (gen_sub (fun s hs => (hsub s hs).1) hmem)


/-! ## Table arithmetic

Composition of packed words. `mulT` is eager: it produces a word, not a
closure, so a word of a hundred letters costs a hundred `mulT` calls and the
result is then applied in constant time. That is what a *generator* wants,
because a generator is evaluated once and applied thousands of times. The
sifting below wants the opposite and gets it another way; see `memChain`. -/

public theorem allLt_of (f : Nat → Bool) : ∀ m : Nat, (∀ k, k < m → f k = true) →
    allLt f m = true := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [allLt_succ, Bool.and_eq_true]
    exact ⟨h n (Nat.lt_succ_self n), ih (fun k hk => h k (Nat.lt_succ_of_lt hk))⟩

public theorem ap_lt (t j : Nat) : ap t j < 128 := Nat.mod_lt _ (by decide)

/-- The identity word. -/
@[expose] public def idT : Nat := pak (fun i => i) 120

/-- Composition of packed words: `(mulT t u) i = t (u i)`. -/
@[expose] public def mulT (t u : Nat) : Nat := pak (fun i => ap t (ap u i)) 120

public theorem ap_idT {i : Nat} (hi : i < 120) : ap idT i = i :=
  ap_pak _ 120 (fun _k hk => Nat.lt_trans hk (by decide)) i hi

public theorem ap_mulT (t u : Nat) {i : Nat} (hi : i < 120) :
    ap (mulT t u) i = ap t (ap u i) :=
  ap_pak _ 120 (fun _k _ => ap_lt _ _) i hi

public theorem tabOK_of {f b : Nat}
    (h1 : ∀ i, i < 120 → ap f i < 120) (h2 : ∀ i, i < 120 → ap b i < 120)
    (h3 : ∀ i, i < 120 → ap b (ap f i) = i) (h4 : ∀ i, i < 120 → ap f (ap b i) = i) :
    tabOK f b = true := by
  refine allLt_of _ 120 (fun k hk => ?_)
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨Nat.ble_eq_true_of_le (h1 k hk), Nat.ble_eq_true_of_le (h2 k hk)⟩, ?_⟩, ?_⟩
  · rw [h3 k hk]; exact Nat.beq_refl k
  · rw [h4 k hk]; exact Nat.beq_refl k

public theorem tabOK_idT : tabOK idT idT = true :=
  tabOK_of (fun i hi => by rw [ap_idT hi]; exact hi) (fun i hi => by rw [ap_idT hi]; exact hi)
    (fun _i hi => by rw [ap_idT hi, ap_idT hi]) (fun _i hi => by rw [ap_idT hi, ap_idT hi])

public theorem tperm_idT : tperm idT idT = Perm.one 120 :=
  Perm.ext fun i => Fin.eq_of_val_eq (by
    rw [tperm_toFun tabOK_idT, ap_idT i.isLt]
    rfl)

public theorem tabOK_swap {f b : Nat} (h : tabOK f b = true) : tabOK b f = true :=
  tabOK_of (fun _i hi => tabOK_bwd h hi) (fun _i hi => tabOK_fwd h hi)
    (fun _i hi => tabOK_right h hi) (fun _i hi => tabOK_left h hi)

public theorem tperm_swap {f b : Nat} (h : tabOK f b = true) :
    tperm b f = (tperm f b).inv :=
  Perm.ext fun i => Fin.eq_of_val_eq (by
    rw [tperm_toFun (tabOK_swap h)]
    show ap b i.val = ((tperm f b).invFun i).val
    rw [tperm_invFun h])

public theorem tabOK_mul {f b f' b' : Nat} (h : tabOK f b = true) (h' : tabOK f' b' = true) :
    tabOK (mulT f f') (mulT b' b) = true := by
  refine tabOK_of (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
  · rw [ap_mulT _ _ hi]
    exact tabOK_fwd h (tabOK_fwd h' hi)
  · rw [ap_mulT _ _ hi]
    exact tabOK_bwd h' (tabOK_bwd h hi)
  · have hlt : ap (mulT f f') i < 120 := by
      rw [ap_mulT _ _ hi]; exact tabOK_fwd h (tabOK_fwd h' hi)
    rw [ap_mulT _ _ hlt, ap_mulT _ _ hi, tabOK_left h (tabOK_fwd h' hi), tabOK_left h' hi]
  · have hlt : ap (mulT b' b) i < 120 := by
      rw [ap_mulT _ _ hi]; exact tabOK_bwd h' (tabOK_bwd h hi)
    rw [ap_mulT _ _ hlt, ap_mulT _ _ hi, tabOK_right h' (tabOK_bwd h hi), tabOK_right h hi]

public theorem tperm_mul {f b f' b' : Nat} (h : tabOK f b = true) (h' : tabOK f' b' = true) :
    tperm (mulT f f') (mulT b' b) = (tperm f b).comp (tperm f' b') :=
  Perm.ext fun i => Fin.eq_of_val_eq (by
    rw [tperm_toFun (tabOK_mul h h'), ap_mulT _ _ i.isLt]
    show ap f (ap f' i.val) = ((tperm f b).toFun ((tperm f' b').toFun i)).val
    rw [tperm_toFun h, tperm_toFun h'])
/-! ## Words

A group element is presented as a word in the generators: letter `2k` is
generator `k` and letter `2k+1` its inverse. `evalT` runs the word on packed
words and `evalP` on `Perm`s, and `evalP_permsOf` says the two agree. `Gen` is
then free -- `gen_evalP` -- so a transversal computed by search still carries
the proof that its entries lie in the group. -/

@[expose] public def tpermP (q : Nat × Nat) : Perm 120 := tperm q.1 q.2

/-- The permutations a list of certified packed words describes. -/
@[expose] public def permsOf (gs : List (Nat × Nat)) : List (Perm 120) := gs.map tpermP

/-- All entries of a table list describe permutations. -/
@[expose] public def TabsOK (gs : List (Nat × Nat)) : Prop := ∀ p ∈ gs, tabOK p.1 p.2 = true

public theorem getD_mem_or {α : Type} (d : α) :
    ∀ (l : List α) (n : Nat), l.getD n d = d ∨ l.getD n d ∈ l := by
  intro l
  induction l with
  | nil => intro _; exact Or.inl rfl
  | cons a as ih =>
    intro n
    cases n with
    | zero => exact Or.inr (List.mem_cons_self ..)
    | succ m =>
      rcases ih m with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

public theorem getD_permsOf (gs : List (Nat × Nat)) (k : Nat) :
    (permsOf gs).getD k (Perm.one 120) = tpermP (gs.getD k (idT, idT)) := by
  induction gs generalizing k with
  | nil => exact tperm_idT.symm
  | cons a as ih =>
    cases k with
    | zero => rfl
    | succ m => exact ih m

@[expose] public def genT (gs : List (Nat × Nat)) (l : Nat) : Nat × Nat :=
  if l % 2 = 0 then gs.getD (l / 2) (idT, idT)
  else ((gs.getD (l / 2) (idT, idT)).2, (gs.getD (l / 2) (idT, idT)).1)

@[expose] public def evalT (gs : List (Nat × Nat)) : List Nat → Nat × Nat
  | [] => (idT, idT)
  | l :: w =>
    match evalT gs w, genT gs l with
    | (f, b), (gf, gb) => (mulT gf f, mulT b gb)

@[expose] public def genP (gs : List (Perm 120)) (l : Nat) : Perm 120 :=
  if l % 2 = 0 then gs.getD (l / 2) (Perm.one 120) else (gs.getD (l / 2) (Perm.one 120)).inv

@[expose] public def evalP (gs : List (Perm 120)) : List Nat → Perm 120
  | [] => Perm.one 120
  | l :: w => (genP gs l).comp (evalP gs w)

public theorem tabOK_genT {gs : List (Nat × Nat)} (hgs : TabsOK gs) (l : Nat) :
    tabOK (genT gs l).1 (genT gs l).2 = true := by
  have hd : tabOK (gs.getD (l / 2) (idT, idT)).1 (gs.getD (l / 2) (idT, idT)).2 = true := by
    rcases getD_mem_or (idT, idT) gs (l / 2) with h | h
    · rw [h]; exact tabOK_idT
    · exact hgs _ h
  rw [genT]
  split
  · exact hd
  · exact tabOK_swap hd

/-- Naming the head step of `evalT` keeps the unifier out of `mulT`: without
it, matching a goal against `tabOK (mulT _ _) (mulT _ _)` sends the elaborator
into the hundred and twenty steps of `pak`. -/
public theorem evalT_cons (gs : List (Nat × Nat)) (l : Nat) (w : List Nat) :
    evalT gs (l :: w)
      = (mulT (genT gs l).1 (evalT gs w).1, mulT (evalT gs w).2 (genT gs l).2) := rfl

public theorem tabOK_evalT {gs : List (Nat × Nat)} (hgs : TabsOK gs) :
    ∀ w : List Nat, tabOK (evalT gs w).1 (evalT gs w).2 = true := by
  intro w
  induction w with
  | nil => exact tabOK_idT
  | cons l w ih =>
    rw [evalT_cons]
    exact tabOK_mul (tabOK_genT hgs l) ih

public theorem genP_permsOf {gs : List (Nat × Nat)} (hgs : TabsOK gs) (l : Nat) :
    genP (permsOf gs) l = tpermP (genT gs l) := by
  have hd : tabOK (gs.getD (l / 2) (idT, idT)).1 (gs.getD (l / 2) (idT, idT)).2 = true := by
    rcases getD_mem_or (idT, idT) gs (l / 2) with h | h
    · rw [h]; exact tabOK_idT
    · exact hgs _ h
  rw [genP, genT, getD_permsOf]
  split
  · rfl
  · exact (tperm_swap hd).symm

public theorem evalP_permsOf {gs : List (Nat × Nat)} (hgs : TabsOK gs) :
    ∀ w : List Nat, evalP (permsOf gs) w = tpermP (evalT gs w) := by
  intro w
  induction w with
  | nil => exact tperm_idT.symm
  | cons l w ih =>
    show (genP (permsOf gs) l).comp (evalP (permsOf gs) w) = tpermP (evalT gs (l :: w))
    rw [genP_permsOf hgs, ih, evalT_cons]
    exact (tperm_mul (tabOK_genT hgs l) (tabOK_evalT hgs w)).symm

public theorem gen_genP (gp : List (Perm 120)) (l : Nat) : Perm.Gen gp (genP gp l) := by
  rw [genP]
  rcases getD_mem_or (Perm.one 120) gp (l / 2) with h | h
  · rw [h]
    split
    · exact Perm.Gen.one
    · exact Perm.Gen.one
  · split
    · exact Perm.Gen.mem_gen h
    · exact Perm.Gen.mem_gen_inv h

public theorem gen_evalP (gp : List (Perm 120)) : ∀ w : List Nat, Perm.Gen gp (evalP gp w) := by
  intro w
  induction w with
  | nil => exact Perm.Gen.one
  | cons l w ih => exact Perm.Gen.comp_mem (gen_genP gp l) ih


/-! ## Orbits and transversals by search

The orbit of a base point, and with it a coset representative for each orbit
element as a *word*, is found by search over the generators and their inverses.
Nothing about the search is proved: every property the counting theorem needs
-- that the list is duplicate-free, closed under the generators, and that the
recorded word really carries the base point to the recorded point -- is checked
afterwards by `decide +kernel`. What the word buys is the one property that
cannot be checked, namely that the representative lies in the group.

The search carries the points already reached as a bit mask instead of
re-scanning the list it is building, and pushes new points onto the front
instead of appending. Both are the same economy: walking a list of a hundred
and twenty costs the kernel about half a megabyte of retained term, and the
search would walk two thousand of them. -/

/-- Bit `y` of a mask. -/
@[expose] public def bitOn (m y : Nat) : Bool := Nat.beq (Nat.mod (Nat.shiftRight m y) 2) 1

/-- One step of the search: apply every generator and every inverse to `p`,
recording the images not seen before. -/
@[expose] public def bfsStep (gt : List (Nat × Nat)) (p : Nat × List Nat)
    (a0 : Nat × List (Nat × List Nat)) : Nat × List (Nat × List Nat) :=
  (List.range (2 * gt.length)).foldl
    (fun a l =>
      match bitOn a.1 (ap (genT gt l).1 p.1) with
      | true => a
      | false => (Nat.lor a.1 (Nat.shiftLeft 1 (ap (genT gt l).1 p.1)),
          (ap (genT gt l).1 p.1, l :: p.2) :: a.2))
    a0

@[expose] public def bfsGo (gt : List (Nat × Nat)) :
    Nat → Nat → List (Nat × List Nat) → List (Nat × List Nat) → List (Nat × List Nat)
  | 0, _, _, done => done
  | _ + 1, _, [], done => done
  | fuel + 1, msk, p :: todo, done =>
    match bfsStep gt p (msk, []) with
    | (msk', new) => bfsGo gt fuel msk' (new ++ todo) (p :: done)

@[expose] public def bfs (gt : List (Nat × Nat)) (b : Nat) (fuel : Nat) :
    List (Nat × List Nat) :=
  bfsGo gt fuel (Nat.shiftLeft 1 b) [(b, [])] []

/-! ## The stabiliser chain as data

A `Level` carries the generators of `G_i` as packed words, the base point
`b_i`, the words over those generators presenting the generators of `G_{i+1}`,
and -- this is the point -- the orbit of `b_i` *stored*: one entry per orbit
point, each with a word carrying the base point there and that word's value as
a packed pair, together with the orbit as a bit mask.

Deriving the orbit instead of storing it is what makes the certificate
unaffordable. `levelCheck` reads the transversal about two thousand times per
level, and `memChain` reads every level below it once per Schreier generator; a
derived orbit re-runs the search on each of those reads, and the kernel
memoises nothing across a `decide`. Stored, the search runs once per level.

Storing it is sound for the reason everything else here is sound: the stored
orbit is *checked*. `levelCheck` verifies that it contains the base point, that
its points are duplicate-free class indices, that each stored representative
carries the base point to its own point, that the mask and the list agree, and
that the point set is closed under the generators -- exactly the list of
properties Schreier's lemma consumes. The one property that cannot be checked,
that a representative lies in the group, is carried by the stored *word*, and
`mkOrb` builds `tb` as that word's value, so `Formed` is a fact about the
chain's shape rather than a kernel computation.

Sifting carries the group element as a *function* rather than as a table. A
level of the descent wraps one more `ap` around it, so applying it costs one
shift per level, where forming the product table would cost a hundred and
twenty. `Agree` is the bridge to the permutation the function denotes, and the
lemmas below are the only place a `Perm` appears. -/

@[expose] public def fin120 (n : Nat) : Fin 120 := ⟨n % 120, Nat.mod_lt _ (by decide)⟩

public theorem fin120_val {n : Nat} (h : n < 120) : (fin120 n).val = n := Nat.mod_eq_of_lt h

/-- One point of a level's orbit, with its coset representative. -/
public structure Cos where
  /-- The orbit point, as a class index. -/
  pt : Nat
  /-- A word over the level's generators carrying the base point to `pt`. -/
  wd : List Nat
  /-- The value of `wd`: the coset representative, as a packed pair. -/
  tb : Nat × Nat

/-- The stored entry for a point, if there is one. -/
@[expose] public def cosAt : List Cos → Nat → Option Cos
  | [], _ => none
  | c :: cs, y =>
    match Nat.beq c.pt y with
    | true => some c
    | false => cosAt cs y

@[expose] public def hasPtC (L : List Cos) (y : Nat) : Bool := (cosAt L y).isSome

/-- The stored orbit points are pairwise distinct. -/
@[expose] public def nodupOrb : List Cos → Bool
  | [] => true
  | c :: cs => Bool.not (hasPtC cs c.pt) && nodupOrb cs

/-- The orbit as a bit mask. -/
@[expose] public def mkMask : List Cos → Nat
  | [] => 0
  | c :: cs => Nat.lor (Nat.shiftLeft 1 c.pt) (mkMask cs)

public structure Level where
  /-- The generators of this level's group, as packed words. -/
  gt : List (Nat × Nat)
  /-- The base point stabilised at this level. -/
  bp : Nat
  /-- Words over `gt` generating the next level's group. -/
  nw : List (List Nat)
  /-- The orbit of `bp` with its transversal, searched once by `mkOrb`. -/
  orb : List Cos
  /-- The same orbit as a bit mask, for the closure check. -/
  msk : Nat

namespace Level

/-- The base point. -/
@[expose] public def basePt (l : Level) : Fin 120 := fin120 l.bp

/-- The orbit of the base point. -/
@[expose] public def orbFin (l : Level) : List (Fin 120) := l.orb.map (fun c => fin120 c.pt)

/-- The stored coset representative carrying the base point to `y`. -/
@[expose] public def trQ (l : Level) (y : Nat) : Nat × Nat :=
  match cosAt l.orb y with
  | some c => c.tb
  | none => (idT, idT)

/-- The coset representative as a permutation. -/
@[expose] public def trP (l : Level) (y : Fin 120) : Perm 120 := tpermP (l.trQ y.val)

/-- The next level's generators, as packed words. -/
@[expose] public def nextGt (l : Level) : List (Nat × Nat) := l.nw.map (evalT l.gt)

/-- The stored representatives are the values of the stored words. `mkOrb`
builds them that way, so this never costs a kernel reduction. -/
@[expose] public def Formed (l : Level) : Prop := ∀ c ∈ l.orb, c.tb = evalT l.gt c.wd

end Level

/-- Sifting: the membership test the chain provides. The element stays a
function of the point, so descending a level wraps one `ap` around it. -/
@[expose] public def memChain : List Level → (Nat → Nat) → Bool
  | [], f => allLt (fun i => Nat.beq (f i) i) 120
  | l :: rest, f =>
    match cosAt l.orb (f l.bp) with
    | none => false
    | some c => memChain rest (fun i => ap c.tb.2 (f i))

/-- Everything about one level that a kernel check can settle. -/
@[expose] public def levelCheck (l : Level) (rest : List Level) : Bool :=
  Nat.blt l.bp 120 &&
  hasPtC l.orb l.bp &&
  Nat.beq (l.trQ l.bp).1 idT &&
  nodupOrb l.orb &&
  l.orb.all (fun c => Nat.blt c.pt 120 && Nat.beq (ap c.tb.1 l.bp) c.pt) &&
  allLt (fun y => Bool.or (Bool.not (bitOn l.msk y)) (hasPtC l.orb y)) 120 &&
  l.orb.all (fun c => l.gt.all (fun s =>
    bitOn l.msk (ap s.1 c.pt) && bitOn l.msk (ap s.2 c.pt))) &&
  l.nextGt.all (fun s => Nat.beq (ap s.1 l.bp) l.bp) &&
  l.orb.all (fun c => l.gt.all (fun s =>
    memChain rest (fun i => ap (l.trQ (ap s.1 c.pt)).2 (ap s.1 (ap c.tb.1 i)))))

/-- The orbit of a base point with its transversal, searched once. -/
@[expose] public def mkOrb (gt : List (Nat × Nat)) (b : Nat) : List Cos :=
  (bfs gt b 200).map (fun p => ⟨p.1, p.2, evalT gt p.2⟩)

/-- The chain a base-point-and-words specification describes. -/
@[expose] public def mkChain : List (Nat × Nat) → List (Nat × List (List Nat)) → List Level
  | _, [] => []
  | gt, (b, nw) :: rest =>
    ⟨gt, b, nw, mkOrb gt b, mkMask (mkOrb gt b)⟩ :: mkChain (nw.map (evalT gt)) rest

/-- The chain's kernel check: every level, and a trivial group at the bottom.

The recursion runs over the *built* chain, and this is what makes the check
affordable. Recursing over the specification instead would build the tail chain
once as the argument of `levelCheck` and then build it again in the recursive
call, so the bottom level would be constructed once per branch of a binary tree
of depth seven. Checking a chain that was built once shares every level between
the two uses -- and, now that the orbit is a field, shares the seven searches
too. -/
@[expose] public def chainCheck : List (Nat × Nat) → List Level → Bool
  | gt, [] => gt.isEmpty
  | _, l :: rest => levelCheck l rest && chainCheck l.nextGt rest

/-- The product of the orbit lengths. -/
@[expose] public def chainLen : List Level → Nat
  | [] => 1
  | l :: rest => l.orb.length * chainLen rest

/-- The permutation a sifting function denotes. -/
@[expose] public def Agree (f : Nat → Nat) (g : Perm 120) : Prop :=
  ∀ i : Fin 120, (g.toFun i).val = f i.val

/-! ### Reading the stored orbit

Nothing below runs in the kernel: these lemmas turn the `Bool` checks of
`levelCheck` into the `Perm`-level hypotheses `hasOrder_step` consumes. -/

public theorem gen_nil_iff (g : Perm 120) : Perm.Gen [] g ↔ g = Perm.one 120 := by
  constructor
  · intro hg
    induction hg with
    | one => rfl
    | step _ hs _ => exact absurd hs (by simp)
    | stepInv _ hs _ => exact absurd hs (by simp)
  · intro hg
    exact hg ▸ Perm.Gen.one

public theorem isEmpty_nil {gt : List (Nat × Nat)} (h : gt.isEmpty = true) : gt = [] := by
  cases gt with
  | nil => rfl
  | cons _ _ => exact absurd h (by simp)

public theorem tabsOK_nextGt {gt : List (Nat × Nat)} (h : TabsOK gt) (nw : List (List Nat)) :
    TabsOK (nw.map (evalT gt)) := by
  intro q hq
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hq
  exact tabOK_evalT h w

public theorem gen_nextGt {gt : List (Nat × Nat)} (h : TabsOK gt) {nw : List (List Nat)}
    {s : Perm 120} (hs : s ∈ permsOf (nw.map (evalT gt))) : Perm.Gen (permsOf gt) s := by
  rw [permsOf, List.map_map] at hs
  obtain ⟨w, _, hw⟩ := List.mem_map.mp hs
  rw [← hw]
  show Perm.Gen (permsOf gt) (tpermP (evalT gt w))
  rw [← evalP_permsOf h]
  exact gen_evalP _ _

/-- A chain built by `mkChain` is `Formed` by construction. -/
public theorem mkOrb_form {l : Level} (h : l.orb = mkOrb l.gt l.bp) : l.Formed := by
  intro c hc
  rw [h] at hc
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
  rfl

/-- A packed pair whose forward table is the identity word is the identity. -/
public theorem tperm_eq_one {f b : Nat} (h : tabOK f b = true) (hf : f = idT) :
    tperm f b = Perm.one 120 := by
  subst hf
  exact Perm.ext fun i => Fin.eq_of_val_eq (by rw [tperm_toFun h, ap_idT i.isLt]; rfl)

public theorem cosAt_some : ∀ (L : List Cos) (y : Nat) (c : Cos),
    cosAt L y = some c → c ∈ L ∧ c.pt = y := by
  intro L
  induction L with
  | nil => intro y c h; exact absurd h (by simp [cosAt])
  | cons d ds ih =>
    intro y c h
    cases hd : Nat.beq d.pt y with
    | true =>
      have h' : some d = some c := by simp only [cosAt, hd] at h; exact h
      have hdc : d = c := Option.some.inj h'
      subst hdc
      exact ⟨List.mem_cons_self .., Nat.eq_of_beq_eq_true hd⟩
    | false =>
      simp only [cosAt, hd] at h
      exact ⟨List.mem_cons_of_mem _ (ih y c h).1, (ih y c h).2⟩

public theorem cosAt_none : ∀ (L : List Cos) (y : Nat),
    cosAt L y = none → ∀ c ∈ L, c.pt ≠ y := by
  intro L
  induction L with
  | nil => intro _ _ c hc; exact absurd hc (by simp)
  | cons d ds ih =>
    intro y h c hc
    cases hd : Nat.beq d.pt y with
    | true =>
      have h' : some d = none := by simp only [cosAt, hd] at h; exact h
      exact absurd h' (by simp)
    | false =>
      have h' : cosAt ds y = none := by simp only [cosAt, hd] at h; exact h
      rcases List.mem_cons.mp hc with rfl | hc'
      · intro he
        rw [he] at hd
        exact absurd (hd.symm.trans (Nat.beq_refl y)) (by decide)
      · exact ih y h' c hc'

public theorem cosAt_of_mem : ∀ (L : List Cos), nodupOrb L = true → ∀ c ∈ L,
    cosAt L c.pt = some c := by
  intro L
  induction L with
  | nil => intro _ c hc; exact absurd hc (by simp)
  | cons d ds ih =>
    intro hnd c hc
    have h1 : (Bool.not (hasPtC ds d.pt) && nodupOrb ds) = true := hnd
    rw [Bool.and_eq_true] at h1
    have hnone : cosAt ds d.pt = none := by
      cases hh : cosAt ds d.pt with
      | none => rfl
      | some _ =>
        have h2 : hasPtC ds d.pt = true := by rw [hasPtC, hh]; rfl
        rw [h2] at h1
        exact absurd h1.1 (by decide)
    rcases List.mem_cons.mp hc with rfl | hc'
    · show (match Nat.beq c.pt c.pt with | true => some c | false => cosAt ds c.pt) = some c
      rw [Nat.beq_refl]
    · have hne : c.pt ≠ d.pt := cosAt_none ds d.pt hnone c hc'
      have hb : Nat.beq d.pt c.pt = false := by
        cases hh : Nat.beq d.pt c.pt with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true hh).symm hne
      show (match Nat.beq d.pt c.pt with | true => some d | false => cosAt ds c.pt) = some c
      rw [hb]
      exact ih h1.2 c hc'

public theorem nodup_orbFin : ∀ L : List Cos, nodupOrb L = true → (∀ c ∈ L, c.pt < 120) →
    (L.map (fun c => fin120 c.pt)).Nodup := by
  intro L
  induction L with
  | nil => intro _ _; exact List.nodup_nil
  | cons c cs ih =>
    intro hnd hlt
    have h1 : (Bool.not (hasPtC cs c.pt) && nodupOrb cs) = true := hnd
    rw [Bool.and_eq_true] at h1
    have hnone : cosAt cs c.pt = none := by
      cases hh : cosAt cs c.pt with
      | none => rfl
      | some _ =>
        have h2 : hasPtC cs c.pt = true := by rw [hasPtC, hh]; rfl
        rw [h2] at h1
        exact absurd h1.1 (by decide)
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, ih h1.2 (fun d hd => hlt d (List.mem_cons_of_mem _ hd))⟩
    intro hmem
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp hmem
    refine cosAt_none cs c.pt hnone d hd ?_
    have hv : (fin120 d.pt).val = (fin120 c.pt).val := congrArg Fin.val hde
    rwa [fin120_val (hlt d (List.mem_cons_of_mem _ hd)),
      fin120_val (hlt c (List.mem_cons_self ..))] at hv

public theorem trQ_of_cosAt {l : Level} {y : Nat} {c : Cos} (h : cosAt l.orb y = some c) :
    l.trQ y = c.tb := by
  simp only [Level.trQ, h]

public theorem trQ_of_mem {l : Level} (hnd : nodupOrb l.orb = true) {c : Cos}
    (hc : c ∈ l.orb) : l.trQ c.pt = c.tb :=
  trQ_of_cosAt (cosAt_of_mem l.orb hnd c hc)

public theorem tabOK_trQ {l : Level} (hgt : TabsOK l.gt) (hf : l.Formed) (y : Nat) :
    tabOK (l.trQ y).1 (l.trQ y).2 = true := by
  cases h : cosAt l.orb y with
  | none => simp only [Level.trQ, h]; exact tabOK_idT
  | some c =>
    rw [trQ_of_cosAt h, hf c (cosAt_some l.orb y c h).1]
    exact tabOK_evalT hgt c.wd

/-- Every coset representative lies in the group, because the stored word does.
This is the one property of the transversal that no kernel check supplies. -/
public theorem trP_gen {l : Level} (hgt : TabsOK l.gt) (hf : l.Formed) (y : Fin 120) :
    Perm.Gen (permsOf l.gt) (l.trP y) := by
  show Perm.Gen (permsOf l.gt) (tpermP (l.trQ y.val))
  cases h : cosAt l.orb y.val with
  | none =>
    simp only [Level.trQ, h]
    show Perm.Gen (permsOf l.gt) (tperm idT idT)
    rw [tperm_idT]
    exact Perm.Gen.one
  | some c =>
    rw [trQ_of_cosAt h, hf c (cosAt_some l.orb y.val c h).1, ← evalP_permsOf hgt]
    exact gen_evalP _ _

public theorem mem_orbFin {l : Level} (hpt : ∀ c ∈ l.orb, c.pt < 120) (y : Fin 120) :
    y ∈ l.orbFin ↔ hasPtC l.orb y.val = true := by
  constructor
  · intro hy
    obtain ⟨c, hc, hcy⟩ := List.mem_map.mp hy
    have hcv : c.pt = y.val := by rw [← hcy]; exact (fin120_val (hpt c hc)).symm
    show (cosAt l.orb y.val).isSome = true
    cases hh : cosAt l.orb y.val with
    | some _ => rfl
    | none => exact absurd hcv (cosAt_none l.orb y.val hh c hc)
  · intro hy
    have h0 : (cosAt l.orb y.val).isSome = true := hy
    cases hh : cosAt l.orb y.val with
    | none => rw [hh] at h0; exact absurd h0 (by decide)
    | some c =>
      obtain ⟨hc, hcy⟩ := cosAt_some l.orb y.val c hh
      exact List.mem_map.mpr ⟨c, hc, Fin.eq_of_val_eq (by rw [fin120_val (hpt c hc), hcy])⟩

/-- The bottom of the chain: a sifting function is the identity exactly when it
fixes all `120` points, which is what `memChain []` tests. -/
public theorem agree_one_iff {f : Nat → Nat} {g : Perm 120} (h : Agree f g) :
    allLt (fun i => Nat.beq (f i) i) 120 = true ↔ g = Perm.one 120 := by
  constructor
  · intro he
    refine Perm.ext fun i => Fin.eq_of_val_eq ?_
    rw [h i]
    exact Nat.eq_of_beq_eq_true (allLt_true _ _ he i.val i.isLt)
  · intro he
    refine allLt_of _ 120 (fun k hk => ?_)
    have hv : f k = k := by
      have h1 := h ⟨k, hk⟩
      rw [he] at h1
      exact h1.symm
    show Nat.beq (f k) k = true
    rw [hv]
    exact Nat.beq_refl k

/-- One level of the descent: wrapping the stored backward table around a
sifting function is dividing by the coset representative. -/
public theorem agree_push {f : Nat → Nat} {g : Perm 120} (h : Agree f g)
    {q : Nat × Nat} (hq : tabOK q.1 q.2 = true) :
    Agree (fun i => ap q.2 (f i)) ((tpermP q).inv.comp g) := by
  intro i
  show ((tperm q.1 q.2).invFun (g.toFun i)).val = ap q.2 (f i.val)
  rw [tperm_invFun hq, h i]

/-- One level of the chain, as the induction below consumes it. -/
public theorem chain_step (l : Level) (rest : List Level) (gt' : List (Nat × Nat)) (N' : Nat)
    (hgt : TabsOK l.gt) (hf : l.Formed) (hnext : gt' = l.nw.map (evalT l.gt))
    (ihmem : ∀ (f : Nat → Nat) (g : Perm 120), Agree f g →
      (memChain rest f = true ↔ Perm.Gen (permsOf gt') g))
    (ihord : HasOrder (permsOf gt') N')
    (hLc : levelCheck l rest = true) :
    (∀ (f : Nat → Nat) (g : Perm 120), Agree f g →
        (memChain (l :: rest) f = true ↔ Perm.Gen (permsOf l.gt) g)) ∧
      HasOrder (permsOf l.gt) (l.orb.length * N') := by
  simp only [levelCheck, Bool.and_eq_true] at hLc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩ := hLc
  have hbp : l.bp < 120 := Nat.le_of_ble_eq_true c1
  have hbase : l.basePt.val = l.bp := fin120_val hbp
  have hpt : ∀ c ∈ l.orb, c.pt < 120 := fun c hc =>
    Nat.le_of_ble_eq_true (Bool.and_eq_true _ _ |>.mp (List.all_eq_true.mp c5 c hc)).1
  have hcarry : ∀ c ∈ l.orb, ap c.tb.1 l.bp = c.pt := fun c hc =>
    Nat.eq_of_beq_eq_true (Bool.and_eq_true _ _ |>.mp (List.all_eq_true.mp c5 c hc)).2
  have htab : ∀ y : Nat, tabOK (l.trQ y).1 (l.trQ y).2 = true := tabOK_trQ hgt hf
  have hb : l.basePt ∈ l.orbFin := (mem_orbFin hpt l.basePt).mpr (by rw [hbase]; exact c2)
  have hnd : l.orbFin.Nodup := nodup_orbFin l.orb c4 hpt
  have hmask : ∀ y, y < 120 → bitOn l.msk y = true → hasPtC l.orb y = true := by
    intro y hy hy'
    have h2 : Bool.or (Bool.not (bitOn l.msk y)) (hasPtC l.orb y) = true :=
      allLt_true _ _ c6 y hy
    rw [hy'] at h2
    exact h2
  have htb : l.trP l.basePt = Perm.one 120 := by
    show tperm (l.trQ l.basePt.val).1 (l.trQ l.basePt.val).2 = Perm.one 120
    rw [hbase]
    exact tperm_eq_one (htab l.bp) (Nat.eq_of_beq_eq_true c3)
  have horb : ∀ y ∈ l.orbFin, ∃ c ∈ l.orb, c.pt = y.val := by
    intro y hy
    obtain ⟨c, hc, hcy⟩ := List.mem_map.mp hy
    exact ⟨c, hc, by rw [← hcy]; exact (fin120_val (hpt c hc)).symm⟩
  have hti : ∀ y ∈ l.orbFin,
      Perm.Gen (permsOf l.gt) (l.trP y) ∧ (l.trP y).toFun l.basePt = y := by
    intro y hy
    obtain ⟨c, hc, hcv⟩ := horb y hy
    refine ⟨trP_gen hgt hf y, Fin.eq_of_val_eq ?_⟩
    show ((tperm (l.trQ y.val).1 (l.trQ y.val).2).toFun l.basePt).val = y.val
    rw [tperm_toFun (htab y.val), hbase, ← hcv, trQ_of_mem c4 hc]
    exact hcarry c hc
  have hOc : ∀ y ∈ l.orbFin, ∀ s ∈ permsOf l.gt,
      s.toFun y ∈ l.orbFin ∧ s.invFun y ∈ l.orbFin := by
    intro y hy s hs
    obtain ⟨c, hc, hcv⟩ := horb y hy
    obtain ⟨q, hq, hqs⟩ := List.mem_map.mp hs
    have hqt : tabOK q.1 q.2 = true := hgt q hq
    have hck := Bool.and_eq_true _ _ |>.mp
      (List.all_eq_true.mp (List.all_eq_true.mp c7 c hc) q hq)
    subst hqs
    have hf1 : ((tpermP q).toFun y).val = ap q.1 y.val := tperm_toFun hqt y
    have hf2 : ((tpermP q).invFun y).val = ap q.2 y.val := tperm_invFun hqt y
    refine ⟨(mem_orbFin hpt _).mpr ?_, (mem_orbFin hpt _).mpr ?_⟩
    · rw [hf1, ← hcv]
      exact hmask _ (by rw [hcv]; exact tabOK_fwd hqt y.isLt) hck.1
    · rw [hf2, ← hcv]
      exact hmask _ (by rw [hcv]; exact tabOK_bwd hqt y.isLt) hck.2
  have hsub : ∀ s ∈ permsOf gt',
      Perm.Gen (permsOf l.gt) s ∧ s.toFun l.basePt = l.basePt := by
    intro s hs
    rw [hnext] at hs
    obtain ⟨q, hq, hqs⟩ := List.mem_map.mp hs
    have hqt : tabOK q.1 q.2 = true := tabsOK_nextGt hgt l.nw q hq
    refine ⟨gen_nextGt hgt hs, ?_⟩
    subst hqs
    refine Fin.eq_of_val_eq ?_
    show ((tperm q.1 q.2).toFun l.basePt).val = l.basePt.val
    rw [tperm_toFun hqt, hbase]
    exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp c8 q hq)
  have hsch : ∀ y ∈ l.orbFin, ∀ s ∈ permsOf l.gt,
      Perm.Gen (permsOf gt') ((l.trP (s.toFun y)).inv.comp (s.comp (l.trP y))) := by
    intro y hy s hs
    obtain ⟨c, hc, hcv⟩ := horb y hy
    obtain ⟨q, hq, hqs⟩ := List.mem_map.mp hs
    have hqt : tabOK q.1 q.2 = true := hgt q hq
    subst hqs
    have hcb : tabOK c.tb.1 c.tb.2 = true := by
      have h := htab c.pt
      rw [trQ_of_mem c4 hc] at h
      exact h
    have e1 : ((tpermP q).toFun y).val = ap q.1 c.pt := by
      show ((tperm q.1 q.2).toFun y).val = ap q.1 c.pt
      rw [tperm_toFun hqt, hcv]
    have e2 : l.trP y = tperm c.tb.1 c.tb.2 := by
      show tpermP (l.trQ y.val) = tperm c.tb.1 c.tb.2
      rw [← hcv, trQ_of_mem c4 hc]
      rfl
    have e3 : l.trP ((tpermP q).toFun y)
        = tperm (l.trQ (ap q.1 c.pt)).1 (l.trQ (ap q.1 c.pt)).2 := by
      show tpermP (l.trQ ((tpermP q).toFun y).val) = _
      rw [e1]
      rfl
    have hag : Agree (fun i => ap (l.trQ (ap q.1 c.pt)).2 (ap q.1 (ap c.tb.1 i)))
        ((l.trP ((tpermP q).toFun y)).inv.comp ((tpermP q).comp (l.trP y))) := by
      intro i
      show ((l.trP ((tpermP q).toFun y)).invFun
          ((tperm q.1 q.2).toFun ((l.trP y).toFun i))).val
        = ap (l.trQ (ap q.1 c.pt)).2 (ap q.1 (ap c.tb.1 i.val))
      rw [e2, e3, tperm_invFun (htab (ap q.1 c.pt)), tperm_toFun hqt, tperm_toFun hcb]
    exact (ihmem _ _ hag).mp (List.all_eq_true.mp (List.all_eq_true.mp c9 c hc) q hq)
  refine ⟨fun f g hag => ?_, ?_⟩
  · have hval : (g.toFun l.basePt).val = f l.bp := by rw [hag l.basePt, hbase]
    have hiff := gen_iff_step hb htb hti hOc hsub hsch g
    show (match cosAt l.orb (f l.bp) with
          | none => false
          | some c => memChain rest (fun i => ap c.tb.2 (f i))) = true
        ↔ Perm.Gen (permsOf l.gt) g
    cases hcos : cosAt l.orb (f l.bp) with
    | none =>
      have hnot : g.toFun l.basePt ∉ l.orbFin := by
        intro hmem
        have h0 := (mem_orbFin hpt _).mp hmem
        rw [hval, hasPtC, hcos] at h0
        exact absurd h0 (by decide)
      constructor
      · intro h
        exact absurd (show (false : Bool) = true from h) (by decide)
      · intro h; exact absurd (hiff.mp h).1 hnot
    | some c =>
      have hmem : g.toFun l.basePt ∈ l.orbFin := by
        refine (mem_orbFin hpt _).mpr ?_
        rw [hval, hasPtC, hcos]
        rfl
      have htr : l.trP (g.toFun l.basePt) = tpermP c.tb := by
        show tpermP (l.trQ (g.toFun l.basePt).val) = tpermP c.tb
        rw [hval, trQ_of_cosAt hcos]
      have hcb : tabOK c.tb.1 c.tb.2 = true := by
        have h := htab (f l.bp)
        rw [trQ_of_cosAt hcos] at h
        exact h
      have hag' : Agree (fun i => ap c.tb.2 (f i))
          ((l.trP (g.toFun l.basePt)).inv.comp g) := by
        rw [htr]
        exact agree_push hag hcb
      rw [ihmem _ _ hag', hiff]
      exact ⟨fun h => ⟨hmem, h⟩, fun h => h.2⟩
  · have h := hasOrder_step hb hnd htb hti hOc hsub hsch ihord
    have hlen : l.orbFin.length = l.orb.length := by simp [Level.orbFin]
    rwa [hlen] at h

/-- **The stabiliser chain is correct.** Sifting decides membership in the
group the chain's top level generates, and the product of the orbit lengths is
that group's order. -/
public theorem mkChain_spec :
    ∀ (spec : List (Nat × List (List Nat))) (gt : List (Nat × Nat)),
      TabsOK gt → chainCheck gt (mkChain gt spec) = true →
      (∀ (f : Nat → Nat) (g : Perm 120), Agree f g →
          (memChain (mkChain gt spec) f = true ↔ Perm.Gen (permsOf gt) g)) ∧
        HasOrder (permsOf gt) (chainLen (mkChain gt spec)) := by
  intro spec
  induction spec with
  | nil =>
    intro gt _ hc
    have hgt : gt = [] := isEmpty_nil hc
    subst hgt
    refine ⟨fun f g hag => ?_, hasOrder_nil⟩
    show allLt (fun i => Nat.beq (f i) i) 120 = true ↔ Perm.Gen [] g
    rw [gen_nil_iff]
    exact agree_one_iff hag
  | cons a rest ih =>
    intro gt hgt hc
    obtain ⟨b, nw⟩ := a
    -- `Level.nextGt ⟨gt, b, nw, _, _⟩` is `nw.map (evalT gt)` by projection, so
    -- the unfolded check is literally the conjunction the induction consumes.
    have hc' : (levelCheck ⟨gt, b, nw, mkOrb gt b, mkMask (mkOrb gt b)⟩
          (mkChain (nw.map (evalT gt)) rest) &&
        chainCheck (nw.map (evalT gt)) (mkChain (nw.map (evalT gt)) rest)) = true := hc
    rw [Bool.and_eq_true] at hc'
    have hnx : TabsOK (nw.map (evalT gt)) := tabsOK_nextGt hgt nw
    obtain ⟨ihmem, ihord⟩ := ih (nw.map (evalT gt)) hnx hc'.2
    exact chain_step ⟨gt, b, nw, mkOrb gt b, mkMask (mkOrb gt b)⟩
      (mkChain (nw.map (evalT gt)) rest) (nw.map (evalT gt)) _ hgt (mkOrb_form rfl) rfl
      ihmem ihord hc'.1

/-! ## `D21` and `T28`: the automorphism group and its order

`Aut` is `< s_a : a in Sim >`. The chain below has base points
`0, 1, 2, 4, 6, 8, 10` and orbit lengths `120, 63, 24, 10, 8, 6, 4`, whose
product is `348364800`. Only the base points and the words presenting each
level's generators are supplied; the orbits, the transversals and the check
that the seventh stabiliser is trivial are all computed and verified here. -/

/-- The eight reflection generators as packed words. -/
@[expose] public def autGt : List (Nat × Nat) := D20lit.map (fun t => (t, t))

public theorem autGt_ok : TabsOK autGt := by
  intro q hq
  obtain ⟨t, ht, hq'⟩ := List.mem_map.mp hq
  rw [← hq']
  exact List.all_eq_true.mp D20litOK t ht

public theorem autGens_eq : permsOf autGt = (List.finRange 8).map D20 := by
  show (D20lit.map (fun t => (t, t))).map tpermP = (List.finRange 8).map D20
  rw [List.map_map, ← D20lit_eq, List.map_map]
  rfl

/-- `D21`. `Aut := < s_a : a in Sim >`, the subgroup of the permutations of the
`120` classes generated by the reflections of `D20`. -/
@[expose] public def D21 : Perm 120 → Prop := Perm.Gen (permsOf autGt)

public theorem D21_iff (g : Perm 120) : D21 g ↔ Perm.Gen ((List.finRange 8).map D20) g := by
  rw [D21, autGens_eq]

/-- Every generator of `D21` is a member of it, and `D21` is a subgroup. This
is not the document's `D21a`, which is about the componentwise action on
AtlasPresentations; it is the group structure `D21` needs to be used as one. -/
public theorem D21_subgroup : (∀ a : Fin 8, D21 (D20 a)) ∧ D21 (Perm.one 120) ∧
    (∀ g h : Perm 120, D21 g → D21 h → D21 (g.comp h)) ∧
    (∀ g : Perm 120, D21 g → D21 g.inv) :=
  ⟨fun a => (D21_iff _).mpr (Perm.Gen.mem_gen (List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩)),
    Perm.Gen.one, fun _ _ hg hh => Perm.Gen.comp_mem hg hh, fun _ hg => Perm.Gen.inv_mem hg⟩

/-- The base points and the words presenting each stabiliser, computed by a
Schreier-Sims run outside the kernel and checked inside it by `autChain`. -/
@[expose] public def autSpec : List (Nat × List (List Nat)) :=
  [(0, [[0], [8, 14, 5], [7, 3, 5, 7, 9, 6, 4, 2, 6, 11, 12]]),
   (1, [[1, 5, 0, 4, 0, 3], [1, 3, 4, 3, 5, 1, 4, 1, 3, 4, 0, 4, 0, 2, 5, 0, 2]]),
   (2, [[3, 1, 3, 3, 0, 0], [1, 2, 2, 1]]),
   (4, [[2, 1, 3], [2, 2, 1, 2]]),
   (6, [[2, 0, 2, 2], [1]]),
   (8, [[1, 3, 3, 0], [0, 2]]),
   (10, [])]

set_option maxHeartbeats 4000000 in
/-- The chain of `autSpec` is a stabiliser chain for `Aut`.

The heartbeat budget is lifted for the two certificate checks below, and only
for them. `decide +kernel` hands the reduction to the kernel, which has no
heartbeat limit, but the elaborator still builds the term it hands over, and at
`120` points with seven levels that walk exceeds the default. The budget bounds
elaboration effort; it is not a proof obligation, and lifting it weakens
nothing --- the kernel still checks the result. -/
public theorem autChain : chainCheck autGt (mkChain autGt autSpec) = true := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- The seven orbit lengths multiply to `348364800`. -/
public theorem autChainLen : chainLen (mkChain autGt autSpec) = 348364800 := by decide +kernel

/-- `T28`. `|Aut| = 348364800`. -/
public theorem T28 : HasOrder (permsOf autGt) 348364800 := by
  have h := (mkChain_spec autSpec autGt autGt_ok autChain).2
  rwa [autChainLen] at h

/-! ## `T59p0` and `T59p`: `Aut` inside the graph automorphisms

`D13` makes the `120` classes a graph, and `D21`'s generators are reflections
of the root system, so they permute the classes preserving inner products up to
sign and hence preserving adjacency. `T59p0` checks that for the eight
generators in the kernel; `T59p` propagates it to all of `Aut` by induction on
the generation, which is the containment `Aut <= Aut(G)` that `T59` and `T60`
are read inside. -/

/-- The base of the packed adjacency table: `2 ^ 120`, one row. -/
@[expose] public def adjBase : Nat := Nat.shiftLeft 1 120

public theorem adjBase_eq : adjBase = 2 ^ 120 := by
  show (1 : Nat) <<< 120 = 2 ^ 120
  rw [Nat.shiftLeft_eq, Nat.one_mul]

/-- The adjacency of `D13` as one packed table of `120` rows of `120` bits.
`T59p0` asks for adjacency `230400` times, and one `adjN` costs two inner
products against the class words. Packed, the kernel pays for the `14400`
distinct entries once. Reading is two levels because a row is `j`-independent:
the row shift out of the `14400`-bit table happens once per generator and
vertex, and each of the `120` bits of that row is then a shift of a small
number. -/
@[expose] public def adjPack : Nat := pk adjBase (fun i => pk 2 (fun j => adjN i j) 120) 120

/-- Row `i` of `adjPack`. -/
@[expose] public def adjRow (i : Nat) : Nat :=
  Nat.mod (Nat.shiftRight adjPack (Nat.mul 120 i)) adjBase

/-- Bit `j` of row `i`. -/
@[expose] public def adjBit (i j : Nat) : Nat := Nat.mod (Nat.shiftRight (adjRow i) j) 2

public theorem adjRaw_lt (i j : Nat) : adjRaw i j < 2 := by
  show (if dot8 (repN i) (repN j) = 4 then 1
    else if dot8 (repN i) (repN j) = -4 then 1 else 0) < 2
  split
  · decide
  · split
    · decide
    · decide

public theorem adjN_lt (i j : Nat) : adjN i j < 2 := by
  show (if i = j then 0 else if i < j then adjRaw i j else adjRaw j i) < 2
  split
  · decide
  · split
    · exact adjRaw_lt i j
    · exact adjRaw_lt j i

public theorem adjRow_eq {i : Nat} (hi : i < 120) :
    adjRow i = pk 2 (fun j => adjN i j) 120 := by
  show adjPack >>> (120 * i) % adjBase = _
  rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ (120 * i) = adjBase ^ i by
    rw [adjBase_eq, ← Nat.pow_mul]]
  exact pk_digit adjBase (by rw [adjBase_eq]; exact Nat.two_pow_pos 120) _ 120
    (fun k _ => by
      rw [adjBase_eq]
      exact pk_lt 2 _ 120 (fun j _ => adjN_lt k j)) i hi

public theorem adjBit_eq {i j : Nat} (hi : i < 120) (hj : j < 120) :
    adjBit i j = adjN i j := by
  show adjRow i >>> j % 2 = adjN i j
  rw [Nat.shiftRight_eq_div_pow, adjRow_eq hi]
  exact pk_digit 2 (by decide) _ 120 (fun k _ => adjN_lt i k) j hj

set_option maxHeartbeats 4000000 in
/-- `T59p0`. Every reflection generator preserves the adjacency of `D13`. -/
public theorem T59p0 : D20lit.all (fun t =>
    allLt (fun i => allLt (fun j =>
      Nat.beq (adjBit (ap t i) (ap t j)) (adjBit i j)) 120) 120) = true := by
  decide +kernel

public theorem D20_adj (a : Fin 8) (u v : K) :
    A ((D20 a).toFun u) ((D20 a).toFun v) = A u v := by
  show adjN ((D20 a).toFun u).val ((D20 a).toFun v).val = adjN u.val v.val
  have hlu : ap (D20tab a) u.val < 120 := tabOK_fwd (D20tabOK a) u.isLt
  have hlv : ap (D20tab a) v.val < 120 := tabOK_fwd (D20tabOK a) v.isLt
  rw [show ((D20 a).toFun u).val = ap (D20tab a) u.val from tperm_toFun (D20tabOK a) u,
    show ((D20 a).toFun v).val = ap (D20tab a) v.val from tperm_toFun (D20tabOK a) v,
    ← adjBit_eq hlu hlv, ← adjBit_eq u.isLt v.isLt]
  exact Nat.eq_of_beq_eq_true (allLt_true _ _
    (allLt_true _ _ (List.all_eq_true.mp T59p0 _ (D20tab_mem a)) u.val u.isLt) v.val v.isLt)

public theorem gensP_adj {s : Perm 120} (hs : s ∈ permsOf autGt) (u v : K) :
    A (s.toFun u) (s.toFun v) = A u v := by
  rw [autGens_eq] at hs
  obtain ⟨a, _, ha⟩ := List.mem_map.mp hs
  rw [← ha]
  exact D20_adj a u v

/-- `T59p`. Every automorphism of `D21` is an automorphism of the class graph
`D13`: `Aut <= Aut(G)`. -/
public theorem T59p {g : Perm 120} (hg : D21 g) :
    ∀ u v : K, A (g.toFun u) (g.toFun v) = A u v := by
  rw [D21] at hg
  induction hg with
  | one => intro u v; rfl
  | @step p s _ hs ih =>
    intro u v
    show A (p.toFun (s.toFun u)) (p.toFun (s.toFun v)) = A u v
    rw [ih, gensP_adj hs]
  | @stepInv p s _ hs ih =>
    intro u v
    show A (p.toFun (s.invFun u)) (p.toFun (s.invFun v)) = A u v
    rw [ih]
    have h := gensP_adj hs (s.invFun u) (s.invFun v)
    rw [s.right_inv, s.right_inv] at h
    exact h.symm


/-! ## `V66`: the reflections are unimodular, permute `R`, and fix the form -/

/-- Componentwise equality of vectors as a `Bool`, so that a vector identity
can be one entry of a kernel certificate. -/
@[expose] public def vecEq8 (u v : Vec 8 Int) : Bool :=
  allFin (fun m : Fin 8 => decide (u m = v m))

public theorem vecEq8_eq {u v : Vec 8 Int} (h : vecEq8 u v = true) : u = v :=
  funext fun m => of_decide_eq_true (allFin_true _ h m)

set_option maxHeartbeats 1000000 in
/-- The three facts `V66b` and `V66c` read off, checked on all `240` roots:
`r_a` carries a root to a root, is an involution there, and pairs every root
with every simple root in a multiple of `4`. The last is what makes the
division in `D20vec` exact, and it is the only place the `2x` scaling of the
form enters the reflection formula. -/
public theorem V66comp : allFin (fun i : Fin 240 => allFin (fun a : Fin 8 =>
    isD11 (D20vec a (R240 i))
      && vecEq8 (D20vec a (D20vec a (R240 i))) (R240 i)
      && decide (dot (R240 i) (D19a a) % 4 = 0))) = true := by decide +kernel

public theorem V66comp_at (i : Fin 240) (a : Fin 8) :
    D11 (D20vec a (R240 i))
      ∧ D20vec a (D20vec a (R240 i)) = R240 i
      ∧ dot (R240 i) (D19a a) % 4 = 0 := by
  have h := allFin_true _ (allFin_true _ V66comp i) a
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨(isD11_iff _).mp h.1.1, vecEq8_eq h.1.2, of_decide_eq_true h.2⟩

/-- `V66b`. Each `r_a` **permutes `R`**: it carries roots to roots, and it is
an involution on them, so it is a bijection of `R` onto itself. -/
public theorem V66b (a : Fin 8) :
    (∀ x : Vec 8 Int, D11 x → D11 (D20vec a x))
      ∧ (∀ x : Vec 8 Int, D11 x → D20vec a (D20vec a x) = x) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, rfl⟩ := T5.2.2 x hx
    exact (V66comp_at i a).1
  · obtain ⟨i, rfl⟩ := T5.2.2 x hx
    exact (V66comp_at i a).2.1

/-- The bilinear expansion of a reflection: this is `<x - c a, y - d a>`
written out, and it is the only algebra `V66c` needs. -/
public theorem dot_reflect (c d : Int) (x y a : Vec 8 Int) :
    dot (fun j => x j - c * a j) (fun j => y j - d * a j)
      = dot x y - d * dot x a - c * dot a y + c * d * dot a a := by
  have h : ∀ i : Fin 8, (x i - c * a i) * (y i - d * a i)
      = x i * y i + ((-d) * (x i * a i) + ((-c) * (a i * y i) + (c * d) * (a i * a i))) := by
    intro i; grind
  show Vec.sumInt (fun i => (x i - c * a i) * (y i - d * a i)) = _
  rw [Glue.sumInt_congr h, Glue.sumInt_add, Glue.sumInt_add, Glue.sumInt_add,
    Glue.sumInt_mul_left, Glue.sumInt_mul_left, Glue.sumInt_mul_left]
  show dot x y + ((-d) * dot x a + ((-c) * dot a y + c * d * dot a a)) = _
  grind

/-- `V66c`. Each `r_a` **preserves the bilinear form** on `R`. -/
public theorem V66c (a : Fin 8) (x y : Vec 8 Int) (hx : D11 x) (hy : D11 y) :
    dot (D20vec a x) (D20vec a y) = dot x y := by
  obtain ⟨i, rfl⟩ := T5.2.2 x hx
  obtain ⟨j, rfl⟩ := T5.2.2 y hy
  have hxd := (V66comp_at i a).2.2
  have hyd := (V66comp_at j a).2.2
  have hnorm : dot (D19a a) (D19a a) = 8 := (V65a.1 a).2
  have hcx : 4 * (dot (R240 i) (D19a a) / 4) = dot (R240 i) (D19a a) :=
    Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hxd)
  have hcy : 4 * (dot (R240 j) (D19a a) / 4) = dot (R240 j) (D19a a) :=
    Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hyd)
  have hsym : dot (D19a a) (R240 j) = dot (R240 j) (D19a a) := dot_comm _ _
  show dot (fun m => R240 i m - (dot (R240 i) (D19a a) / 4) * D19a a m)
      (fun m => R240 j m - (dot (R240 j) (D19a a) / 4) * D19a a m) = _
  rw [dot_reflect, hnorm, hsym]
  grind

/-- `V66a`. Each `r_a` is **integral in the `Sim` basis, with determinant
`-1`**: in the coordinates of the `V65c` basis it is the integer matrix
`reflMat` of `D41`, and its determinant is `-1`, so it lies in `GL_8(Z)`. -/
public theorem V66a : ∀ j : Fin 8,
    (∀ c : Vec 8 Int, Places.reflCoord j c = Mat.apply (Places.reflMat j) c)
      ∧ det (Places.reflMat j) = -1 := by
  refine fun j => ⟨Places.reflCoord_eq j, ?_⟩
  revert j
  decide +kernel

/-! ## `V67`: `pi(r_a) = s_a` -/

/-- `pi` on a map of the lattice: the map of classes it induces, `k(x)` going
to `k(f(x))`. `D42` is the same map read on `Sim` coordinates; this is the
form the packed permutations of `D20` are stated in. -/
@[expose] public def piK (f : Vec 8 Int → Vec 8 Int) (i : K) : K := D12 (f (rep i))

/-- `V67`. `pi(r_a) = s_a` for every `a` in `Sim`: the class map induced by the
reflection formula `D20vec` is the packed permutation `D20`. The two are
different objects -- `D20` is a table, checked against `D19a`, `rep` and `D12`
by `D20lit_eq` -- so this is a statement relating them and not an unfolding. -/
public theorem V67 (a : Fin 8) : piK (D20vec a) = (D20 a).toFun :=
  funext fun i => (D20_apply a i).symm


/-! ## The action of `Aut` on class subsets -/

/-- The image of the classes of `W` below `m` under `f`. -/
@[expose] public def imgN (f : Nat → Nat) (W : Bitset) (m : Nat) : Bitset :=
  Nat.rec (motive := fun _ => Bitset) Bitset.empty
    (fun k ih => match Bitset.mem W k with
      | true => Bitset.union (Bitset.singleton (f k)) ih
      | false => ih) m

public theorem imgN_succ_pos (f : Nat → Nat) (W : Bitset) {m : Nat} (h : Bitset.mem W m = true) :
    imgN f W (m + 1) = Bitset.union (Bitset.singleton (f m)) (imgN f W m) := by
  show (match Bitset.mem W m with
    | true => Bitset.union (Bitset.singleton (f m)) (imgN f W m)
    | false => imgN f W m) = _
  rw [h]

public theorem imgN_succ_neg (f : Nat → Nat) (W : Bitset) {m : Nat} (h : Bitset.mem W m = false) :
    imgN f W (m + 1) = imgN f W m := by
  show (match Bitset.mem W m with
    | true => Bitset.union (Bitset.singleton (f m)) (imgN f W m)
    | false => imgN f W m) = _
  rw [h]

public theorem mem_imgN (f : Nat → Nat) (W : Bitset) :
    ∀ (m i : Nat), i ∈ imgN f W m ↔ ∃ j, j < m ∧ j ∈ W ∧ f j = i := by
  intro m
  induction m with
  | zero =>
    intro i
    constructor
    · intro h; exact absurd h (Bitset.notMem_empty i)
    · rintro ⟨j, hj, -, -⟩; exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro i
    cases hk : Bitset.mem W k with
    | true =>
      rw [imgN_succ_pos f W hk, Bitset.mem_union, Bitset.mem_singleton, ih i]
      constructor
      · rintro (rfl | ⟨j, hj, hjW, hji⟩)
        · exact ⟨k, Nat.lt_succ_self k, hk, rfl⟩
        · exact ⟨j, Nat.lt_succ_of_lt hj, hjW, hji⟩
      · rintro ⟨j, hj, hjW, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact Or.inr ⟨j, h, hjW, rfl⟩
        · exact Or.inl rfl
    | false =>
      rw [imgN_succ_neg f W hk, ih i]
      constructor
      · rintro ⟨j, hj, hjW, hji⟩
        exact ⟨j, Nat.lt_succ_of_lt hj, hjW, hji⟩
      · rintro ⟨j, hj, hjW, hji⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact ⟨j, h, hjW, hji⟩
        · exact absurd (show Bitset.mem W j = true from hjW) (by rw [hk]; decide)

public theorem imgN_congr {f f' : Nat → Nat} (W : Bitset) :
    ∀ (m : Nat), (∀ j, j < m → f j = f' j) → imgN f W m = imgN f' W m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    cases hk : Bitset.mem W k with
    | true =>
      rw [imgN_succ_pos f W hk, imgN_succ_pos f' W hk, h k (Nat.lt_succ_self k),
        ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]
    | false =>
      rw [imgN_succ_neg f W hk, imgN_succ_neg f' W hk,
        ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]

/-- `g.W`: the image of a set of classes under an automorphism. -/
@[expose] public def actP (g : Perm 120) (W : Bitset) : Bitset :=
  imgN (fun j => (g.toFun (fin120 j)).val) W 120

/-- The same image, driven by a packed word. This is the form every kernel
certificate below runs. -/
@[expose] public def actT (t : Nat) (W : Bitset) : Bitset := imgN (ap t) W 120

public theorem mem_actP (g : Perm 120) (W : Bitset) (i : Nat) :
    i ∈ actP g W ↔ ∃ u : K, u.val ∈ W ∧ (g.toFun u).val = i := by
  rw [actP, mem_imgN]
  constructor
  · rintro ⟨j, hj, hjW, hji⟩
    refine ⟨⟨j, hj⟩, hjW, ?_⟩
    have he : (⟨j, hj⟩ : Fin 120) = fin120 j := Fin.eq_of_val_eq (fin120_val hj).symm
    rw [he]
    exact hji
  · rintro ⟨u, huW, hui⟩
    refine ⟨u.val, u.isLt, huW, ?_⟩
    have he : fin120 u.val = u := Fin.eq_of_val_eq (fin120_val u.isLt)
    rw [he]
    exact hui

public theorem actT_eq {f b : Nat} (h : tabOK f b = true) (W : Bitset) :
    actT f W = actP (tperm f b) W :=
  imgN_congr W 120 (fun j hj => by
    rw [tperm_toFun h, fin120_val hj])

public theorem actP_one {W : Bitset} (hW : Blocks.ClassSet W) : actP (Perm.one 120) W = W := by
  refine Bitset.ext (fun i => ?_)
  rw [mem_actP]
  constructor
  · rintro ⟨u, huW, rfl⟩; exact huW
  · intro hi
    exact ⟨⟨i, Blocks.lt_of_mem hW hi⟩, hi, rfl⟩

public theorem actP_comp (g h : Perm 120) (W : Bitset) :
    actP (g.comp h) W = actP g (actP h W) := by
  refine Bitset.ext (fun i => ?_)
  rw [mem_actP, mem_actP]
  constructor
  · rintro ⟨u, huW, rfl⟩
    exact ⟨h.toFun u, (mem_actP h W _).mpr ⟨u, huW, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, huW, hu⟩ := (mem_actP h W v.val).mp hv
    refine ⟨u, huW, ?_⟩
    show (g.toFun (h.toFun u)).val = (g.toFun v).val
    rw [Fin.eq_of_val_eq hu]

/-- Acting by `g` and then by its inverse returns the set. -/
public theorem actP_inv (g : Perm 120) {W : Bitset} (hW : Blocks.ClassSet W) :
    actP g.inv (actP g W) = W := by
  rw [← actP_comp, Perm.inv_comp, actP_one hW]

public theorem classSet_actP (g : Perm 120) (W : Bitset) : Blocks.ClassSet (actP g W) := by
  show Bitset.toNat (actP g W) < 2 ^ 120
  refine Nat.lt_pow_two_of_testBit _ (fun i hi => ?_)
  have hno : ¬ (i ∈ actP g W) := by
    intro hm
    obtain ⟨u, -, hu⟩ := (mem_actP g W i).mp hm
    exact absurd (hu ▸ (g.toFun u).isLt) (by omega)
  exact Bool.not_eq_true _ |>.mp hno

/-! ## Section 10: the gauge group of an instance

`D21a`, `D28`, `D28a`, `D29` and `D30` are declared here, in the module that
owns `D21` and `actP` and runs the stabiliser chain on them. They were first
written in a separate downstream module, which forced a second copy of the
predicate here -- `D28` cannot be stated without `D21`, and the chain
certificates cannot be stated without `D28`. Two copies of one definition are
what `R4` forbids and what the duplication gate caught, so the definitions live
where their certificates do and the downstream module is gone. -/

/-- `D28`. `D28(W) := Stab_Aut(W)`, the gauge group of an instance: the
automorphisms of `Aut` carrying the class set `W` onto itself.

The document warns this must not be written `Aut(Atlas)`: by `T46` the
categorical object has exactly one endomorphism. They are different objects and
this library keeps them apart by construction -- `D28` is a predicate on
`Perm 120`, while the categorical endomorphism monoid lives in `Category` over
`AtlasAction` and shares no declaration with it. -/
@[expose] public def D28 (W : Bitset) (g : Perm 120) : Prop := D21 g ∧ actP g W = W

/-- `D28(W)` is a subgroup of `Aut`. -/
public theorem D28_group {W : Bitset} (hW : Blocks.ClassSet W) :
    D28 W (Perm.one 120)
      ∧ (∀ g h : Perm 120, D28 W g → D28 W h → D28 W (g.comp h))
      ∧ (∀ g : Perm 120, D28 W g → D28 W g.inv) := by
  refine ⟨⟨Perm.Gen.one, actP_one hW⟩, fun g h hg hh => ⟨Perm.Gen.comp_mem hg.1 hh.1, ?_⟩,
    fun g hg => ⟨Perm.Gen.inv_mem hg.1, ?_⟩⟩
  · rw [actP_comp, hh.2, hg.2]
  · have h1 : actP g.inv (actP g W) = W := by
      rw [← actP_comp, Perm.inv_comp, actP_one hW]
    rw [hg.2] at h1
    exact h1

/-! ## The witness AtlasInstance in exposed data

`Blocks.A0` is not `@[expose]`, so `V(A_0)` does not reduce outside its own
module and no kernel certificate can mention it. `W0` is the same set of
classes written in the data that is exposed -- the four blocks -- and `W0_eq`
is the identification, read off the enumeration `vIdx` that `Blocks` proves
lists exactly the classes of `V(A_0)`. Every certificate below runs on `W0`
and every statement is about `V(A_0)`. -/

/-- The witness AtlasInstance: the union of the four blocks of `A_0`. -/
@[expose] public def W0 : Bitset := Blocks.union4 Blocks.blkSet

public theorem classSet_W0 : Blocks.ClassSet W0 :=
  Blocks.classSet_union
    (Blocks.classSet_union (Blocks.blkIsBlock 0).1 (Blocks.blkIsBlock 1).1)
    (Blocks.classSet_union (Blocks.blkIsBlock 2).1 (Blocks.blkIsBlock 3).1)

public theorem W0comp :
    allLt (fun j => Bitset.mem W0 (Blocks.vIdx j)) 48 = true
      ∧ allLt (fun c => !(Bitset.mem W0 c)
          || (decide (Blocks.vFind c < 48) && decide (Blocks.vIdx (Blocks.vFind c) = c))) 120
        = true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- `W0` is `V(A_0)`: both are listed by `vIdx`. -/
public theorem W0_eq : Blocks.V Blocks.A0 = W0 := by
  refine Bitset.ext (fun i => ⟨fun hi => ?_, fun hi => ?_⟩)
  · have hlt : i < 120 := Blocks.lt_of_mem (Blocks.classSet_V Blocks.A0) hi
    have h := allLt_true _ _ Blocks.vIdxComp.2.2 i hlt
    have hm : Bitset.mem (Blocks.V Blocks.A0) i = true := hi
    rw [hm] at h
    have h2 : (decide (Blocks.vFind i < 48) && decide (Blocks.vIdx (Blocks.vFind i) = i))
        = true := by simpa using h
    rw [Bool.and_eq_true] at h2
    have hf : Blocks.vFind i < 48 := of_decide_eq_true h2.1
    have hv : Blocks.vIdx (Blocks.vFind i) = i := of_decide_eq_true h2.2
    have hw := allLt_true _ _ W0comp.1 (Blocks.vFind i) hf
    rw [hv] at hw
    exact hw
  · have hlt : i < 120 := Blocks.lt_of_mem classSet_W0 hi
    have h := allLt_true _ _ W0comp.2 i hlt
    have hm : Bitset.mem W0 i = true := hi
    rw [hm] at h
    have h2 : (decide (Blocks.vFind i < 48) && decide (Blocks.vIdx (Blocks.vFind i) = i))
        = true := by simpa using h
    rw [Bool.and_eq_true] at h2
    have hf : Blocks.vFind i < 48 := of_decide_eq_true h2.1
    have hv : Blocks.vIdx (Blocks.vFind i) = i := of_decide_eq_true h2.2
    have h3 := (Bool.and_eq_true _ _ |>.mp
      (allLt_true _ _ Blocks.vIdxComp.1 (Blocks.vFind i) hf)).2
    rw [hv] at h3
    exact h3

/-! ## `V76` and `V77`: a stabiliser element exchanging the two frames

The word below was found by a search outside the kernel -- the orbit of the
witness AtlasInstance under the eight reflections, with a coset word recorded
for each of its members, and one Schreier generator read off an edge that
closes. Nothing about the search is assumed: the word is *evaluated* here by
`evalT`, so it lies in `Aut` because it is a word, and everything it is
claimed to do to the blocks is checked by `decide +kernel`. -/

/-- A word over the generators of `D20`, letter `2k` being generator `k`. -/
@[expose] public def swapWord : List Nat :=
  [0, 4, 10, 8, 6, 4, 14, 12, 10, 8, 14, 10, 12, 2, 6, 8, 10, 2, 6, 4, 2, 0]

/-- Its value, as a packed pair. -/
@[expose] public def swapQ : Nat × Nat := evalT autGt swapWord

/-- Its value, as a permutation of the classes. -/
@[expose] public def swapPerm : Perm 120 := tpermP swapQ

public theorem swapTabOK : tabOK swapQ.1 swapQ.2 = true := tabOK_evalT autGt_ok swapWord

public theorem swap_gen : D21 swapPerm := by
  show Perm.Gen (permsOf autGt) (tpermP (evalT autGt swapWord))
  rw [← evalP_permsOf autGt_ok]
  exact gen_evalP _ _

public theorem actP_swap (W : Bitset) : actP swapPerm W = actT swapQ.1 W :=
  (actT_eq swapTabOK W).symm

set_option maxHeartbeats 1000000 in
/-- What the word does: it fixes the witness AtlasInstance setwise, exchanges
its two BlockFrames, and carries each block of one frame onto a block of the
other. -/
public theorem swapFacts :
    actT swapQ.1 W0 = W0
      ∧ actT swapQ.1 Blocks.frame0.V = Blocks.frame1.V
      ∧ actT swapQ.1 Blocks.frame1.V = Blocks.frame0.V
      ∧ actT swapQ.1 Blocks.frame0.fst = Blocks.frame1.snd
      ∧ actT swapQ.1 Blocks.frame0.snd = Blocks.frame1.fst
      ∧ actT swapQ.1 Blocks.frame1.fst = Blocks.frame0.snd
      ∧ actT swapQ.1 Blocks.frame1.snd = Blocks.frame0.fst :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The word is in the gauge group of the witness AtlasInstance. -/
public theorem swap_stab : D28 (Blocks.V Blocks.A0) swapPerm := by
  refine ⟨swap_gen, ?_⟩
  rw [W0_eq, actP_swap]
  exact swapFacts.1

/-- `V76`. **Some element of the gauge group exchanges the two frames** of the
witness AtlasInstance. -/
public theorem V76 : ∃ g : Perm 120, D28 (Blocks.V Blocks.A0) g
    ∧ actP g Blocks.frame0.V = Blocks.frame1.V
    ∧ actP g Blocks.frame1.V = Blocks.frame0.V :=
  ⟨swapPerm, swap_stab, by rw [actP_swap]; exact swapFacts.2.1,
    by rw [actP_swap]; exact swapFacts.2.2.1⟩

/-- `V77`. **That element carries the first BlockFrame onto the second**: its
two blocks go to the two blocks of `frame1`, and so its support goes to the
support of `frame1`. -/
public theorem V77 : actP swapPerm Blocks.frame0.fst = Blocks.frame1.snd
    ∧ actP swapPerm Blocks.frame0.snd = Blocks.frame1.fst
    ∧ actP swapPerm Blocks.frame0.V = Blocks.frame1.V :=
  ⟨by rw [actP_swap]; exact swapFacts.2.2.2.1,
    by rw [actP_swap]; exact swapFacts.2.2.2.2.1,
    by rw [actP_swap]; exact swapFacts.2.1⟩



/-! ## The gauge group of the witness instance, by its own stabiliser chain -/

/-- Four elements of `D28(W_0)`, as words over the generators of `D20`. They
were found by a Schreier-Sims run outside the kernel; that they lie in `Aut` is
free, because they are words, and that they fix `W_0` is checked below. -/
@[expose] public def stabWords : List (List Nat) := [[4, 8, 14, 0, 14, 12, 8, 0], [10, 8, 6, 2, 12, 10, 4, 10, 12, 6, 8, 10], [2, 4, 6, 4, 8, 6, 4, 14, 2, 6, 8, 4], [0, 4, 6, 4, 10, 8, 6, 12, 10, 4, 14, 12, 2, 6, 8, 10, 2, 6, 4, 0]]

/-- The same four elements as packed words. -/
@[expose] public def stabGt : List (Nat × Nat) := stabWords.map (evalT autGt)

/-- The base points and the words presenting each stabiliser of the chain for
`< stabGt >`: orbits of `48`, `3`, `8`, `2` and `2`, whose product is `4608`. -/
@[expose] public def stabSpec : List (Nat × List (List Nat)) := [(0, [[0], [3, 0, 2], [5, 1, 2, 0, 4], [5, 1, 4, 0, 4], [7, 5, 0, 4, 6]]), (1, [[0], [2], [4], [6], [9, 0, 8]]), (2, [[1, 6], [3, 0, 4]]), (4, [[0]]), (6, [])]

public theorem stabGt_ok : TabsOK stabGt := tabsOK_nextGt autGt_ok stabWords

set_option maxHeartbeats 4000000 in
public theorem stabChain : chainCheck stabGt (mkChain stabGt stabSpec) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
public theorem stabChainLen : chainLen (mkChain stabGt stabSpec) = 4608 := by decide +kernel

/-- `< stabGt >` has `4608` elements. -/
public theorem stabOrder : HasOrder (permsOf stabGt) 4608 := by
  have h := (mkChain_spec stabSpec stabGt stabGt_ok stabChain).2
  rwa [stabChainLen] at h


/-- Every generator of the chain lies in the gauge group: it is in `Aut`
because it is a word, and it fixes `W_0` by the check below. -/
public theorem stabGt_stab : stabGt.all (fun q => decide (actT q.1 W0 = W0)) = true := by
  decide +kernel

public theorem stabGen_of_mem {s : Perm 120} (hs : s ∈ permsOf stabGt) : D28 W0 s := by
  refine ⟨gen_nextGt autGt_ok hs, ?_⟩
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
  have htab : tabOK q.1 q.2 = true := stabGt_ok q hq
  show actP (tperm q.1 q.2) W0 = W0
  rw [← actT_eq htab]
  exact of_decide_eq_true (List.all_eq_true.mp stabGt_stab q hq)

/-- `< stabGt >` is contained in the gauge group of the witness instance. -/
public theorem stabGen_gauge {g : Perm 120} (hg : Perm.Gen (permsOf stabGt) g) : D28 W0 g := by
  induction hg with
  | one => exact (D28_group classSet_W0).1
  | @step p s _ hs ih =>
    exact (D28_group classSet_W0).2.1 p s ih (stabGen_of_mem hs)
  | @stepInv p s _ hs ih =>
    exact (D28_group classSet_W0).2.1 p s.inv ih
      ((D28_group classSet_W0).2.2 s (stabGen_of_mem hs))

/-! ## The bottom of a stabiliser chain

An element of the group a chain presents that fixes every base point is the
identity: the sifting of `memChain` divides by nothing at each level -- the
transversal at the base point is the identity word, which is what `levelCheck`
checks -- so the element reaches the bottom unchanged, where `memChain []`
tests that it fixes all `120` points. -/

public theorem mkChain_bp : ∀ (spec : List (Nat × List (List Nat))) (gt : List (Nat × Nat)),
    ∀ l ∈ mkChain gt spec, ∃ p ∈ spec, l.bp = p.1 := by
  intro spec
  induction spec with
  | nil => intro gt l hl; exact absurd hl (by simp [mkChain])
  | cons a rest ih =>
    intro gt l hl
    obtain ⟨b, nw⟩ := a
    have hl' : l ∈ (⟨gt, b, nw, mkOrb gt b, mkMask (mkOrb gt b)⟩ : Level)
        :: mkChain (nw.map (evalT gt)) rest := hl
    rcases List.mem_cons.mp hl' with rfl | hm
    · exact ⟨(b, nw), List.mem_cons_self .., rfl⟩
    · obtain ⟨p, hp, hbp⟩ := ih (nw.map (evalT gt)) l hm
      exact ⟨p, List.mem_cons_of_mem _ hp, hbp⟩

/-- The level `mkChain` puts at the head of the chain for `(b, nw) :: rest`. -/
@[expose] public def headLevel (gt : List (Nat × Nat)) (b : Nat) (nw : List (List Nat)) : Level :=
  ⟨gt, b, nw, mkOrb gt b, mkMask (mkOrb gt b)⟩

public theorem mkChain_bp_lt : ∀ (spec : List (Nat × List (List Nat))) (gt : List (Nat × Nat)),
    chainCheck gt (mkChain gt spec) = true → ∀ l ∈ mkChain gt spec, l.bp < 120 := by
  intro spec
  induction spec with
  | nil => intro gt _ l hl; exact absurd hl (by simp [mkChain])
  | cons a rest ih =>
    intro gt hc l hl
    obtain ⟨b, nw⟩ := a
    have hc' : (levelCheck (headLevel gt b nw) (mkChain (nw.map (evalT gt)) rest) &&
        chainCheck (nw.map (evalT gt)) (mkChain (nw.map (evalT gt)) rest)) = true := hc
    rw [Bool.and_eq_true] at hc'
    have hl' : l ∈ headLevel gt b nw :: mkChain (nw.map (evalT gt)) rest := hl
    rcases List.mem_cons.mp hl' with rfl | hm
    · have hL := hc'.1
      simp only [levelCheck, Bool.and_eq_true] at hL
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨c1, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hL
      exact Nat.le_of_ble_eq_true c1
    · exact ih (nw.map (evalT gt)) hc'.2 l hm

public theorem memChain_fix : ∀ (spec : List (Nat × List (List Nat))) (gt : List (Nat × Nat)),
    TabsOK gt → chainCheck gt (mkChain gt spec) = true →
    ∀ f : Nat → Nat, (∀ i, i < 120 → f i < 120) →
      (∀ l ∈ mkChain gt spec, f l.bp = l.bp) →
      memChain (mkChain gt spec) f = true → ∀ i, i < 120 → f i = i := by
  intro spec
  induction spec with
  | nil =>
    intro gt _ _ f _ _ hm i hi
    have h : allLt (fun k => Nat.beq (f k) k) 120 = true := hm
    exact Nat.eq_of_beq_eq_true (allLt_true _ _ h i hi)
  | cons a rest ih =>
    intro gt hgt hc f hlt hfix hm i hi
    obtain ⟨b, nw⟩ := a
    have hc' : (levelCheck (headLevel gt b nw) (mkChain (nw.map (evalT gt)) rest) &&
        chainCheck (nw.map (evalT gt)) (mkChain (nw.map (evalT gt)) rest)) = true := hc
    rw [Bool.and_eq_true] at hc'
    have hL := hc'.1
    simp only [levelCheck, Bool.and_eq_true] at hL
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩ := hL
    have hfb : f (headLevel gt b nw).bp = (headLevel gt b nw).bp :=
      hfix (headLevel gt b nw) (List.mem_cons_self ..)
    have hsome : (cosAt (headLevel gt b nw).orb (headLevel gt b nw).bp).isSome = true := c2
    cases hcos : cosAt (headLevel gt b nw).orb (headLevel gt b nw).bp with
    | none => rw [hcos] at hsome; exact absurd hsome (by decide)
    | some c =>
      have htb : (headLevel gt b nw).trQ (headLevel gt b nw).bp = c.tb := trQ_of_cosAt hcos
      have hone : c.tb.1 = idT := by
        have := Nat.eq_of_beq_eq_true c3
        rwa [htb] at this
      have hok : tabOK c.tb.1 c.tb.2 = true := by
        have := tabOK_trQ hgt (mkOrb_form (l := headLevel gt b nw) rfl) (headLevel gt b nw).bp
        rwa [htb] at this
      have hback : ∀ x, x < 120 → ap c.tb.2 x = x := by
        intro x hx
        have h1 := tabOK_left hok hx
        rwa [hone, ap_idT hx] at h1
      have hmem : memChain (mkChain (nw.map (evalT gt)) rest)
          (fun k => ap c.tb.2 (f k)) = true := by
        have h0 : (match cosAt (headLevel gt b nw).orb (f (headLevel gt b nw).bp) with
            | none => false
            | some c => memChain (mkChain (nw.map (evalT gt)) rest)
                (fun k => ap c.tb.2 (f k))) = true := hm
        rw [hfb, hcos] at h0
        exact h0
      have hbplt : ∀ l' ∈ mkChain (nw.map (evalT gt)) rest, l'.bp < 120 :=
        mkChain_bp_lt rest (nw.map (evalT gt)) hc'.2
      have hfix' : ∀ l' ∈ mkChain (nw.map (evalT gt)) rest,
          (fun k => ap c.tb.2 (f k)) l'.bp = l'.bp := by
        intro l' hl'
        have h1 : f l'.bp = l'.bp := hfix l' (List.mem_cons_of_mem _ hl')
        show ap c.tb.2 (f l'.bp) = l'.bp
        rw [h1]
        exact hback l'.bp (hbplt l' hl')
      exact hback (f i) (hlt i hi) ▸ ih (nw.map (evalT gt)) (tabsOK_nextGt hgt nw) hc'.2
        (fun k => ap c.tb.2 (f k)) (fun k hk => by
          rw [hback (f k) (hlt k hk)]; exact hlt k hk) hfix' hmem i hi

/-- An element of `Aut` fixing the seven base points of `autSpec` is the
identity: `348364800 = 120 * 63 * 24 * 10 * 8 * 6 * 4` is exactly the statement
that the chain's pointwise stabiliser is trivial, and this reads that off the
sifting rather than off the number. -/
public theorem aut_fix_trivial {g : Perm 120} (hg : D21 g)
    (h0 : (g.toFun (fin120 0)).val = 0) (h1 : (g.toFun (fin120 1)).val = 1)
    (h2 : (g.toFun (fin120 2)).val = 2) (h4 : (g.toFun (fin120 4)).val = 4)
    (h6 : (g.toFun (fin120 6)).val = 6) (h8 : (g.toFun (fin120 8)).val = 8)
    (h10 : (g.toFun (fin120 10)).val = 10) : g = Perm.one 120 := by
  have hAgree : Agree (fun i => (g.toFun (fin120 i)).val) g := by
    intro i
    show (g.toFun i).val = (g.toFun (fin120 i.val)).val
    rw [show fin120 i.val = i from Fin.eq_of_val_eq (fin120_val i.isLt)]
  have hm : memChain (mkChain autGt autSpec) (fun i => (g.toFun (fin120 i)).val) = true :=
    ((mkChain_spec autSpec autGt autGt_ok autChain).1 _ g hAgree).mpr hg
  have hlt : ∀ i, i < 120 → (g.toFun (fin120 i)).val < 120 :=
    fun i _ => (g.toFun (fin120 i)).isLt
  have hbs : ∀ b : Nat, b ∈ autSpec.map Prod.fst → (g.toFun (fin120 b)).val = b := by
    intro b hb
    have hb' : b ∈ [0, 1, 2, 4, 6, 8, 10] := hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h4
    · exact h6
    · exact h8
    · exact h10
  have hfix : ∀ l ∈ mkChain autGt autSpec, (g.toFun (fin120 l.bp)).val = l.bp := by
    intro l hl
    obtain ⟨p, hp, hbp⟩ := mkChain_bp autSpec autGt l hl
    rw [hbp]
    exact hbs p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hall := memChain_fix autSpec autGt autGt_ok autChain _ hlt hfix hm
  refine Perm.ext fun i => Fin.eq_of_val_eq ?_
  have hval := hall i.val i.isLt
  rw [show fin120 i.val = i from Fin.eq_of_val_eq (fin120_val i.isLt)] at hval
  exact hval

/-! ## Counting inside an instance

The descent below identifies the image of a base point by counting, inside
`W`, the walks from it to the points already fixed. Two counts do the work:
`cnt2t`, the classes of `W` adjacent to three given classes, and `cnt3`, the
walks of length three inside `W`. Both are invariant under an automorphism
that fixes `W` setwise, because such an automorphism is a bijection of `K`
carrying `W` to `W` and preserving adjacency -- which is `sumK_reindex`,
`ind_actP` and `T59p`, in that order.

Each count is stated twice: once as a sum over `K`, which is what the
invariance proofs run on, and once on bit masks, which is what the kernel
certificates run on. `cnt2b_eq` and `cnt3b_eq` are the bridge. The masked form
matters: a walk count written as a double sum over `K` costs the kernel
fourteen thousand steps per pair, and the certificates ask for it a hundred and
twenty times. -/

/-- A sum over the classes is unchanged by permuting them. -/
public theorem sumK_reindex (g : Perm 120) (h : K → Nat) :
    Vec.sumNat (fun u : K => h (g.toFun u)) = Vec.sumNat h := by
  have key : ∀ H : K → Int, Vec.sum (fun u : K => H (g.toFun u)) = Vec.sum H := by
    intro H
    have e1 : ∀ u : K, H (g.toFun u)
        = Vec.sum (fun v : K => if v = g.toFun u then H v else AddCommGroup.zero) :=
      fun u => (Vec.sum_ite_eq' (g.toFun u) H).symm
    rw [Vec.sum_congr e1, Vec.sum_exchange]
    refine Vec.sum_congr (fun v => ?_)
    have e2 : ∀ u : K, (if v = g.toFun u then H v else AddCommGroup.zero)
        = (if u = g.invFun v then H v else AddCommGroup.zero) := by
      intro u
      by_cases hu : u = g.invFun v
      · rw [if_pos hu, if_pos (show v = g.toFun u by rw [hu, g.right_inv])]
      · refine (if_neg ?_).trans (if_neg hu).symm
        intro he
        exact hu (by rw [he, g.left_inv])
    rw [Vec.sum_congr e2]
    exact Vec.sum_ite_eq' (g.invFun v) (fun _ => H v)
  have h1 := Roots.sumNat_cast (fun u : K => h (g.toFun u))
  have h2 := Roots.sumNat_cast h
  have h3 : Vec.sum (fun u : K => ((h (g.toFun u) : Nat) : Int))
      = Vec.sum (fun u : K => ((h u : Nat) : Int)) := key (fun u : K => ((h u : Nat) : Int))
  have h4 : ((Vec.sumNat (fun u : K => h (g.toFun u)) : Nat) : Int)
      = ((Vec.sumNat h : Nat) : Int) := by rw [h1, h3, h2]
  omega

/-- Membership in a set an automorphism fixes is invariant along it. -/
public theorem mem_actP_iff {g : Perm 120} {W : Bitset} (h : actP g W = W) (u : K) :
    (g.toFun u).val ∈ W ↔ u.val ∈ W := by
  constructor
  · intro hu
    rw [← h] at hu
    obtain ⟨v, hv, hvu⟩ := (mem_actP g W _).mp hu
    have : v = u := Perm.toFun_injective (Fin.eq_of_val_eq hvu)
    rw [this] at hv
    exact hv
  · intro hu
    rw [← h]
    exact (mem_actP g W _).mpr ⟨u, hu, rfl⟩

public theorem ind_actP {g : Perm 120} {W : Bitset} (h : actP g W = W) (u : K) :
    Blocks.ind W (g.toFun u).val = Blocks.ind W u.val := by
  show (if (g.toFun u).val ∈ W then 1 else 0) = (if u.val ∈ W then 1 else 0)
  by_cases hu : u.val ∈ W
  · rw [if_pos hu, if_pos ((mem_actP_iff h u).mpr hu)]
  · rw [if_neg hu, if_neg (fun hc => hu ((mem_actP_iff h u).mp hc))]

/-- The classes of `W` adjacent to all of `u`, `v` and `w`. -/
@[expose] public def cnt2t (W : Bitset) (u v w : K) : Nat :=
  Vec.sumNat (fun y : K => Blocks.ind W y.val * A u y * A v y * A w y)

/-- The classes of `W` adjacent to both `u` and `v`. -/
@[expose] public def cnt2 (W : Bitset) (u v : K) : Nat :=
  Vec.sumNat (fun y : K => Blocks.ind W y.val * A u y * A v y)

/-- The walks `u - x - y - v` with `x`, `y` in `W`. -/
@[expose] public def cnt3 (W : Bitset) (u v : K) : Nat :=
  Vec.sumNat (fun x : K => Blocks.ind W x.val * A u x * cnt2 W x v)

public theorem cnt2t_inv {g : Perm 120} {W : Bitset} (hg : D21 g) (hW : actP g W = W)
    (u v w : K) : cnt2t W (g.toFun u) (g.toFun v) (g.toFun w) = cnt2t W u v w := by
  show Vec.sumNat (fun y : K => Blocks.ind W y.val * A (g.toFun u) y
    * A (g.toFun v) y * A (g.toFun w) y) = _
  rw [← sumK_reindex g (fun y : K => Blocks.ind W y.val * A (g.toFun u) y
    * A (g.toFun v) y * A (g.toFun w) y)]
  refine Vec.sumNat_congr (fun y => ?_)
  rw [ind_actP hW y, T59p hg u y, T59p hg v y, T59p hg w y]

public theorem cnt2_inv {g : Perm 120} {W : Bitset} (hg : D21 g) (hW : actP g W = W)
    (u v : K) : cnt2 W (g.toFun u) (g.toFun v) = cnt2 W u v := by
  show Vec.sumNat (fun y : K => Blocks.ind W y.val * A (g.toFun u) y * A (g.toFun v) y) = _
  rw [← sumK_reindex g (fun y : K => Blocks.ind W y.val * A (g.toFun u) y * A (g.toFun v) y)]
  refine Vec.sumNat_congr (fun y => ?_)
  rw [ind_actP hW y, T59p hg u y, T59p hg v y]

public theorem cnt3_inv {g : Perm 120} {W : Bitset} (hg : D21 g) (hW : actP g W = W)
    (u v : K) : cnt3 W (g.toFun u) (g.toFun v) = cnt3 W u v := by
  show Vec.sumNat (fun x : K => Blocks.ind W x.val * A (g.toFun u) x
    * cnt2 W x (g.toFun v)) = _
  rw [← sumK_reindex g (fun x : K => Blocks.ind W x.val * A (g.toFun u) x
    * cnt2 W x (g.toFun v))]
  refine Vec.sumNat_congr (fun x => ?_)
  rw [ind_actP hW x, T59p hg u x, cnt2_inv hg hW x v]

/-! ### The same counts on bit masks -/

/-- Row `u` of the adjacency table, as a set of classes. -/
@[expose] public def arow (u : Nat) : Bitset := Bitset.ofNat (adjRow u)

public theorem classSet_inter {S T : Bitset} (h : Blocks.ClassSet S) :
    Blocks.ClassSet (Bitset.inter S T) := by
  show Bitset.toNat (Bitset.inter S T) < 2 ^ 120
  refine Nat.lt_pow_two_of_testBit _ (fun i hi => ?_)
  have hno : ¬ (i ∈ Bitset.inter S T) := fun hm =>
    absurd (Blocks.lt_of_mem h ((Bitset.mem_inter S T i).mp hm).1) (by omega)
  exact Bool.not_eq_true _ |>.mp hno

public theorem ind_inter (S T : Bitset) (i : Nat) :
    Blocks.ind (Bitset.inter S T) i = Blocks.ind S i * Blocks.ind T i := by
  show (if i ∈ Bitset.inter S T then 1 else 0)
    = (if i ∈ S then 1 else 0) * (if i ∈ T then 1 else 0)
  by_cases hs : i ∈ S
  · by_cases ht : i ∈ T
    · rw [if_pos ((Bitset.mem_inter S T i).mpr ⟨hs, ht⟩), if_pos hs, if_pos ht]
    · rw [if_neg (fun hm => ht ((Bitset.mem_inter S T i).mp hm).2), if_pos hs, if_neg ht]
  · rw [if_neg (fun hm => hs ((Bitset.mem_inter S T i).mp hm).1), if_neg hs]
    exact (Nat.zero_mul _).symm

/-- Membership in a `Bitset` written as a digit of its numeral, for an
arbitrary numeral: the adjacency table is one, and no proof below may unfold
it. -/
public theorem mem_bitset_iff (n i : Nat) : (i ∈ (Bitset.ofNat n)) ↔ n / 2 ^ i % 2 = 1 := by
  show Nat.testBit n i = true ↔ _
  rw [Nat.testBit_eq_decide_div_mod_eq]
  exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

public theorem mem_adjRow {u i : Nat} (hu : u < 120) (hi : i < 120) :
    (i ∈ arow u) ↔ adjN u i = 1 := by
  rw [show arow u = Bitset.ofNat (adjRow u) from rfl, mem_bitset_iff]
  have hf : adjRow u / 2 ^ i % 2 = adjBit u i := by
    show adjRow u / 2 ^ i % 2 = adjRow u >>> i % 2
    rw [Nat.shiftRight_eq_div_pow]
  rw [hf, adjBit_eq hu hi]

public theorem ind_adjRow {u i : Nat} (hu : u < 120) (hi : i < 120) :
    Blocks.ind (arow u) i = adjN u i := by
  show (if i ∈ arow u then 1 else 0) = adjN u i
  by_cases hm : i ∈ arow u
  · rw [if_pos hm, (mem_adjRow hu hi).mp hm]
  · rw [if_neg hm]
    rcases Nat.lt_or_ge (adjN u i) 1 with h | h
    · exact (Nat.lt_one_iff.mp h).symm
    · exact absurd ((mem_adjRow hu hi).mpr (Nat.le_antisymm (adjN_le_one u i) h)) hm

/-- `cnt2` on bit masks. -/
@[expose] public def cnt2b (W : Bitset) (u v : Nat) : Nat :=
  Bitset.card (Bitset.inter (Bitset.inter W (arow u)) (arow v))

/-- `cnt2t` on bit masks. -/
@[expose] public def cnt2tb (W : Bitset) (u v w : Nat) : Nat :=
  Bitset.card (Bitset.inter (Bitset.inter (Bitset.inter W (arow u)) (arow v)) (arow w))

/-- `cnt3` on bit masks. -/
@[expose] public def cnt3b (W : Bitset) (u v : Nat) : Nat :=
  sumN (fun x => Blocks.ind (Bitset.inter W (arow u)) x * cnt2b W x v) 120

public theorem cnt2b_eq {W : Bitset} (hW : Blocks.ClassSet W) {u v : Nat}
    (hu : u < 120) (hv : v < 120) : cnt2b W u v = cnt2 W ⟨u, hu⟩ ⟨v, hv⟩ := by
  show Bitset.card (Bitset.inter (Bitset.inter W (arow u)) (arow v)) = _
  rw [← Blocks.card_eq_sum_fin (classSet_inter (classSet_inter hW))]
  refine Vec.sumNat_congr (fun y => ?_)
  rw [ind_inter, ind_inter, ind_adjRow hu y.isLt, ind_adjRow hv y.isLt]
  rfl

public theorem cnt2tb_eq {W : Bitset} (hW : Blocks.ClassSet W) {u v w : Nat}
    (hu : u < 120) (hv : v < 120) (hw : w < 120) :
    cnt2tb W u v w = cnt2t W ⟨u, hu⟩ ⟨v, hv⟩ ⟨w, hw⟩ := by
  show Bitset.card (Bitset.inter (Bitset.inter (Bitset.inter W (arow u)) (arow v))
    (arow w)) = _
  rw [← Blocks.card_eq_sum_fin (classSet_inter (classSet_inter (classSet_inter hW)))]
  refine Vec.sumNat_congr (fun y => ?_)
  rw [ind_inter, ind_inter, ind_inter, ind_adjRow hu y.isLt, ind_adjRow hv y.isLt,
    ind_adjRow hw y.isLt]
  rfl

public theorem cnt3b_eq {W : Bitset} (hW : Blocks.ClassSet W) {u v : Nat}
    (hu : u < 120) (hv : v < 120) : cnt3b W u v = cnt3 W ⟨u, hu⟩ ⟨v, hv⟩ := by
  show sumN (fun x => Blocks.ind (Bitset.inter W (arow u)) x * cnt2b W x v) 120 = _
  rw [← sumNat_eq_sumN 120 (fun x => Blocks.ind (Bitset.inter W (arow u)) x * cnt2b W x v)]
  refine Vec.sumNat_congr (fun x => ?_)
  rw [ind_inter, ind_adjRow hu x.isLt, cnt2b_eq hW x.isLt hv]
  rfl

/-! ## `T29`: the gauge group is exactly `< stabGt >`

The chain above counts `< stabGt >`; what remains is that nothing else fixes
`W_0`. The argument is a descent along the base points of `autSpec`. At each
level the element to be identified fixes the points already treated and fixes
`W_0` setwise, so the image of the next base point has the same profile inside
`W_0` as the base point itself: the same membership, the same adjacencies to
the fixed points, the same counts of common neighbours inside `W_0` with pairs
of them, and the same counts of walks of length three inside `W_0` to each of
them. That profile is checked, level by level, to pin the image down to the
transversal points stored below; dividing by the stored transversal element --
a word over `stabGt`, hence a member of `< stabGt >` -- fixes one more base
point. After the seventh level the element fixes all seven, and `aut_fix_trivial`
makes it the identity. -/

/-- The profile of `y` against the already-fixed points `fx`. The cheap tests
come first because `&&` is lazy: the walk count is two orders of magnitude
dearer than an adjacency, and on all but a handful of `y` it is never run. -/
@[expose] public def profOK (fx : List Nat) (b y : Nat) : Bool :=
  Nat.beq (Blocks.ind W0 y) (Blocks.ind W0 b)
    && fx.all (fun f => Nat.beq (adjN y f) (adjN b f))
    && fx.all (fun f => fx.all (fun f' => Nat.beq (cnt2tb W0 y f f') (cnt2tb W0 b f f')))
    && fx.all (fun f => Nat.beq (cnt3b W0 y f) (cnt3b W0 b f))

@[expose] public def hasKey : List (Nat × List Nat) → Nat → Bool
  | [], _ => false
  | (z, _) :: r, y => Nat.beq z y || hasKey r y

@[expose] public def trFind : List (Nat × List Nat) → Nat → List Nat
  | [], _ => []
  | (z, w) :: r, y => match Nat.beq z y with | true => w | false => trFind r y

public theorem trFind_key : ∀ (l : List (Nat × List Nat)) (y : Nat),
    hasKey l y = true → (y, trFind l y) ∈ l := by
  intro l
  induction l with
  | nil =>
    intro y h
    exact absurd (show (false : Bool) = true from h) (by decide)
  | cons p r ih =>
    intro y h
    obtain ⟨z, w⟩ := p
    cases hz : Nat.beq z y with
    | true =>
      have hzy : z = y := Nat.eq_of_beq_eq_true hz
      have he : trFind ((z, w) :: r) y = w := by
        show (match Nat.beq z y with | true => w | false => trFind r y) = w
        rw [hz]
      rw [he, ← hzy]
      exact List.mem_cons_self ..
    | false =>
      have h' : hasKey r y = true := by
        have h0 : (Nat.beq z y || hasKey r y) = true := h
        rw [hz] at h0
        simpa using h0
      have he : trFind ((z, w) :: r) y = trFind r y := by
        show (match Nat.beq z y with | true => w | false => trFind r y) = trFind r y
        rw [hz]
      rw [he]
      exact List.mem_cons_of_mem _ (ih y h')

/-- One level of the descent, as a kernel certificate. -/
@[expose] public def levelOK (fx : List Nat) (b : Nat) (l : List (Nat × List Nat)) : Bool :=
  allLt (fun y => Bool.not (profOK fx b y) || hasKey l y) 120
    && l.all (fun p => Nat.beq (ap (evalT stabGt p.2).1 b) p.1
        && fx.all (fun f => Nat.beq (ap (evalT stabGt p.2).1 f) f))

@[expose] public def trL0 : List (Nat × List Nat) :=
  [(0, []), (1, [2]), (2, [4]), (3, [4, 2]), (4, [6, 4, 0, 4, 6, 0, 4]), (5, [6, 4, 2, 0, 4,
   6, 4, 2]), (6, [4, 6, 2]), (7, [6, 2]), (14, [0, 4]), (15, [0, 4, 2]), (16, [6, 4, 2, 0,
   4, 6, 0, 4]), (17, [6, 4, 0, 4, 6, 4, 2]), (20, [0, 4, 6, 2]), (21, [6]), (26, [4, 6, 4,
   2, 0, 4, 6, 0, 4]), (27, [6, 4, 0, 4, 6, 2]), (32, [4, 6]), (33, [4, 0, 4, 6, 2]), (42,
   [6, 4, 6, 2, 0, 4, 6, 0, 4]), (43, [6, 4, 6, 4, 2, 0, 4, 6, 0, 4]), (44, [6, 0, 4, 6,
   2]), (45, [6, 4, 6, 2]), (46, [6, 0, 4, 6, 4, 2]), (47, [6, 4, 6, 4, 2]), (48, [6, 0, 4,
   6, 0, 4]), (49, [6, 4, 6, 0, 4]), (50, [6, 2, 0, 4, 6, 4, 2]), (51, [6, 4, 6, 0, 4, 2]),
   (52, [6, 2, 0, 4, 6, 0, 4]), (53, [6, 4, 6, 4]), (54, [4, 6, 2, 0, 4, 6, 0, 4]), (55, [6,
   4, 6]), (56, [2, 0, 4, 6, 0, 4]), (63, [4, 2, 0, 4, 6, 0, 4]), (64, [4, 6, 0, 4, 2]),
   (71, [6, 0, 4, 2]), (73, [2, 0, 4, 6, 4, 2]), (78, [6, 0, 4]), (81, [4, 6, 4]), (86, [4,
   0, 4, 6, 4, 2]), (90, [4, 6, 0, 4]), (93, [4, 2, 0, 4, 6, 4, 2]), (98, [0, 4, 6, 4, 2]),
   (101, [6, 4]), (107, [4, 6, 4, 2]), (108, [6, 4, 2]), (115, [0, 4, 6, 0, 4]), (116, [4,
   0, 4, 6, 0, 4])]

@[expose] public def trL1 : List (Nat × List Nat) :=
  [(1, []), (26, [4, 6, 2, 0, 4, 2, 0, 4, 6, 4]), (27, [6, 4, 0, 4, 6])]

@[expose] public def trL2 : List (Nat × List Nat) :=
  [(2, []), (3, [2, 0, 2, 0]), (4, [6, 4, 0, 2, 0, 4, 6]), (5, [6, 4, 0, 2, 0, 4, 6, 2, 0,
   2, 0]), (14, [0]), (15, [2, 0, 2]), (16, [6, 4, 0, 2, 0, 4, 6, 0]), (17, [6, 4, 0, 2, 0,
   4, 6, 2, 0, 2])]

@[expose] public def trL3 : List (Nat × List Nat) :=
  [(4, []), (5, [4, 0, 2, 0, 4, 2, 0, 2, 0])]

@[expose] public def trL4 : List (Nat × List Nat) :=
  [(6, []), (7, [4, 0, 4, 0, 4, 0])]

@[expose] public def trL5 : List (Nat × List Nat) :=
  [(8, [])]

@[expose] public def trL6 : List (Nat × List Nat) :=
  [(10, [])]

/-- The permutation a word over `stabGt` evaluates to. -/
@[expose] public def sOf (w : List Nat) : Perm 120 := tpermP (evalT stabGt w)

public theorem sOf_gen (w : List Nat) : Perm.Gen (permsOf stabGt) (sOf w) := by
  show Perm.Gen (permsOf stabGt) (tpermP (evalT stabGt w))
  rw [← evalP_permsOf stabGt_ok]
  exact gen_evalP _ _

public theorem sOf_apply (w : List Nat) {x : Nat} (hx : x < 120) :
    ((sOf w).toFun (fin120 x)).val = ap (evalT stabGt w).1 x := by
  show ((tperm (evalT stabGt w).1 (evalT stabGt w).2).toFun (fin120 x)).val = _
  rw [tperm_toFun (tabOK_evalT stabGt_ok w), fin120_val hx]

/-! ### The profile is invariant -/

public theorem fixed_fin {g : Perm 120} {f : Nat} (hf : f < 120)
    (hfix : (g.toFun (fin120 f)).val = f) : g.toFun (fin120 f) = fin120 f :=
  Fin.eq_of_val_eq (by rw [hfix, fin120_val hf])

public theorem adjN_image {g : Perm 120} (hg : D21 g) {x f : Nat} (hx : x < 120) (hf : f < 120)
    (hfix : (g.toFun (fin120 f)).val = f) :
    adjN (g.toFun (fin120 x)).val f = adjN x f := by
  have h := T59p hg (fin120 x) (fin120 f)
  rw [fixed_fin hf hfix] at h
  have e1 : A (g.toFun (fin120 x)) (fin120 f) = adjN (g.toFun (fin120 x)).val f := by
    show adjN _ (fin120 f).val = _
    rw [fin120_val hf]
  have e2 : A (fin120 x) (fin120 f) = adjN x f := by
    show adjN (fin120 x).val (fin120 f).val = _
    rw [fin120_val hf, fin120_val hx]
  rw [e1, e2] at h
  exact h

public theorem cnt3b_image {g : Perm 120} (hg : D21 g) (hW : actP g W0 = W0)
    {x f : Nat} (hx : x < 120) (hf : f < 120) (hfix : (g.toFun (fin120 f)).val = f) :
    cnt3b W0 (g.toFun (fin120 x)).val f = cnt3b W0 x f := by
  have hgx : (g.toFun (fin120 x)).val < 120 := (g.toFun (fin120 x)).isLt
  rw [cnt3b_eq classSet_W0 hgx hf, cnt3b_eq classSet_W0 hx hf,
    show (⟨(g.toFun (fin120 x)).val, hgx⟩ : Fin 120) = g.toFun (fin120 x) from
      Fin.eq_of_val_eq rfl,
    show (⟨f, hf⟩ : Fin 120) = fin120 f from Fin.eq_of_val_eq (fin120_val hf).symm,
    show (⟨x, hx⟩ : Fin 120) = fin120 x from Fin.eq_of_val_eq (fin120_val hx).symm]
  have h := cnt3_inv hg hW (fin120 x) (fin120 f)
  rw [fixed_fin hf hfix] at h
  exact h

public theorem cnt2tb_image {g : Perm 120} (hg : D21 g) (hW : actP g W0 = W0)
    {x f f' : Nat} (hx : x < 120) (hf : f < 120) (hf' : f' < 120)
    (hfix : (g.toFun (fin120 f)).val = f) (hfix' : (g.toFun (fin120 f')).val = f') :
    cnt2tb W0 (g.toFun (fin120 x)).val f f' = cnt2tb W0 x f f' := by
  have hgx : (g.toFun (fin120 x)).val < 120 := (g.toFun (fin120 x)).isLt
  rw [cnt2tb_eq classSet_W0 hgx hf hf', cnt2tb_eq classSet_W0 hx hf hf',
    show (⟨(g.toFun (fin120 x)).val, hgx⟩ : Fin 120) = g.toFun (fin120 x) from
      Fin.eq_of_val_eq rfl,
    show (⟨f, hf⟩ : Fin 120) = fin120 f from Fin.eq_of_val_eq (fin120_val hf).symm,
    show (⟨f', hf'⟩ : Fin 120) = fin120 f' from Fin.eq_of_val_eq (fin120_val hf').symm,
    show (⟨x, hx⟩ : Fin 120) = fin120 x from Fin.eq_of_val_eq (fin120_val hx).symm]
  have h := cnt2t_inv hg hW (fin120 x) (fin120 f) (fin120 f')
  rw [fixed_fin hf hfix, fixed_fin hf' hfix'] at h
  exact h

public theorem profOK_image {g : Perm 120} (hg : D21 g) (hW : actP g W0 = W0)
    (fx : List Nat) (hfx : ∀ f ∈ fx, f < 120 ∧ (g.toFun (fin120 f)).val = f)
    {b : Nat} (hb : b < 120) : profOK fx b (g.toFun (fin120 b)).val = true := by
  rw [profOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · have h := ind_actP hW (fin120 b)
    rw [fin120_val hb] at h
    rw [h]
    exact Nat.beq_refl _
  · refine List.all_eq_true.mpr (fun f hf => ?_)
    rw [adjN_image hg (x := b) hb (hfx f hf).1 (hfx f hf).2]
    exact Nat.beq_refl _
  · refine List.all_eq_true.mpr (fun f hf => List.all_eq_true.mpr (fun f' hf' => ?_))
    rw [cnt2tb_image hg hW hb (hfx f hf).1 (hfx f' hf').1 (hfx f hf).2 (hfx f' hf').2]
    exact Nat.beq_refl _
  · refine List.all_eq_true.mpr (fun f hf => ?_)
    rw [cnt3b_image hg hW hb (hfx f hf).1 (hfx f hf).2]
    exact Nat.beq_refl _

set_option maxHeartbeats 4000000 in
public theorem cert0 : levelOK [] 0 trL0 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem cert1 : levelOK [0] 1 trL1 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem cert2 : levelOK [1, 0] 2 trL2 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem cert3 : levelOK [2, 1, 0] 4 trL3 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem cert4 : levelOK [4, 2, 1, 0] 6 trL4 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem cert5 : levelOK [6, 4, 2, 1, 0] 8 trL5 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem cert6 : levelOK [8, 6, 4, 2, 1, 0] 10 trL6 = true := by decide +kernel

/-- Dividing by a transversal element, with the element abstract: it lies in
`< stabGt >`, it agrees with `g` on the next base point, and it fixes the
points already fixed. -/
public theorem descend_of {g t : Perm 120} (hg : D21 g) (hW : actP g W0 = W0)
    (ht : Perm.Gen (permsOf stabGt) t)
    (fx : List Nat) (hfx : ∀ f ∈ fx, f < 120 ∧ (g.toFun (fin120 f)).val = f)
    {b : Nat} (hb : b < 120)
    (htb : (t.toFun (fin120 b)).val = (g.toFun (fin120 b)).val)
    (htf : ∀ f ∈ fx, (t.toFun (fin120 f)).val = f) :
    ∃ g' : Perm 120, g = t.comp g' ∧ D21 g' ∧ actP g' W0 = W0
      ∧ (∀ f ∈ b :: fx, f < 120 ∧ (g'.toFun (fin120 f)).val = f) := by
  have hgauge := stabGen_gauge ht
  have hginv := (D28_group classSet_W0).2.2 _ hgauge
  refine ⟨t.inv.comp g, ?_, ?_, ?_, ?_⟩
  · rw [← Perm.comp_assoc, Perm.comp_inv, Perm.one_comp]
  · exact Perm.Gen.comp_mem (Perm.Gen.inv_mem hgauge.1) hg
  · rw [actP_comp, hW]
    exact hginv.2
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf'
    · refine ⟨hb, ?_⟩
      have h2 : t.invFun (g.toFun (fin120 f)) = fin120 f := by
        rw [← Fin.eq_of_val_eq htb, t.left_inv]
      show (t.invFun (g.toFun (fin120 f))).val = f
      rw [h2, fin120_val hb]
    · refine ⟨(hfx f hf').1, ?_⟩
      have h3 : g.toFun (fin120 f) = t.toFun (fin120 f) :=
        Fin.eq_of_val_eq (by rw [(hfx f hf').2, htf f hf'])
      have h2 : t.invFun (g.toFun (fin120 f)) = fin120 f := by
        rw [h3, t.left_inv]
      show (t.invFun (g.toFun (fin120 f))).val = f
      rw [h2, fin120_val (hfx f hf').1]

/-- One level of the descent: the certificate names the transversal element. -/
public theorem descend_step {g : Perm 120} (hg : D21 g) (hW : actP g W0 = W0)
    (fx : List Nat) (hfx : ∀ f ∈ fx, f < 120 ∧ (g.toFun (fin120 f)).val = f)
    {b : Nat} (hb : b < 120) (l : List (Nat × List Nat)) (hcert : levelOK fx b l = true) :
    ∃ t g' : Perm 120, Perm.Gen (permsOf stabGt) t ∧ g = t.comp g' ∧ D21 g'
      ∧ actP g' W0 = W0 ∧ (∀ f ∈ b :: fx, f < 120 ∧ (g'.toFun (fin120 f)).val = f) := by
  rw [levelOK, Bool.and_eq_true] at hcert
  have hy : (g.toFun (fin120 b)).val < 120 := (g.toFun (fin120 b)).isLt
  have hprof : profOK fx b (g.toFun (fin120 b)).val = true := profOK_image hg hW fx hfx hb
  have hkey : hasKey l (g.toFun (fin120 b)).val = true := by
    have h := allLt_true _ _ hcert.1 (g.toFun (fin120 b)).val hy
    rw [hprof] at h
    simpa using h
  have hw := List.all_eq_true.mp hcert.2 _ (trFind_key l _ hkey)
  rw [Bool.and_eq_true] at hw
  have htb : ((sOf (trFind l (g.toFun (fin120 b)).val)).toFun (fin120 b)).val
      = (g.toFun (fin120 b)).val := by
    rw [sOf_apply _ hb]
    exact Nat.eq_of_beq_eq_true hw.1
  have htf : ∀ f ∈ fx, ((sOf (trFind l (g.toFun (fin120 b)).val)).toFun (fin120 f)).val = f := by
    intro f hf
    rw [sOf_apply _ (hfx f hf).1]
    exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hw.2 f hf)
  obtain ⟨g', hg'⟩ := descend_of hg hW (sOf_gen (trFind l (g.toFun (fin120 b)).val)) fx hfx hb
    htb htf
  exact ⟨sOf (trFind l (g.toFun (fin120 b)).val), g',
    sOf_gen (trFind l (g.toFun (fin120 b)).val), hg'.1, hg'.2.1, hg'.2.2.1, hg'.2.2.2⟩

/-- **The gauge group of the witness instance is exactly the group the chain
counts.** One direction is that every generator is a word fixing `W_0`; the
other is the descent. -/
public theorem gauge_eq (g : Perm 120) : D28 W0 g ↔ Perm.Gen (permsOf stabGt) g := by
  refine ⟨fun h => ?_, fun h => stabGen_gauge h⟩
  obtain ⟨t0, g1, ht0, he0, hg1, hW1, hf1⟩ :=
    descend_step h.1 h.2 [] (fun f hf => absurd hf (by simp)) (by decide : (0:Nat) < 120)
      trL0 cert0
  obtain ⟨t1, g2, ht1, he1, hg2, hW2, hf2⟩ :=
    descend_step hg1 hW1 [0] hf1 (by decide : (1:Nat) < 120) trL1 cert1
  obtain ⟨t2, g3, ht2, he2, hg3, hW3, hf3⟩ :=
    descend_step hg2 hW2 [1, 0] hf2 (by decide : (2:Nat) < 120) trL2 cert2
  obtain ⟨t3, g4, ht3, he3, hg4, hW4, hf4⟩ :=
    descend_step hg3 hW3 [2, 1, 0] hf3 (by decide : (4:Nat) < 120) trL3 cert3
  obtain ⟨t4, g5, ht4, he4, hg5, hW5, hf5⟩ :=
    descend_step hg4 hW4 [4, 2, 1, 0] hf4 (by decide : (6:Nat) < 120) trL4 cert4
  obtain ⟨t5, g6, ht5, he5, hg6, hW6, hf6⟩ :=
    descend_step hg5 hW5 [6, 4, 2, 1, 0] hf5 (by decide : (8:Nat) < 120) trL5 cert5
  obtain ⟨t6, g7, ht6, he6, hg7, hW7, hf7⟩ :=
    descend_step hg6 hW6 [8, 6, 4, 2, 1, 0] hf6 (by decide : (10:Nat) < 120) trL6 cert6
  have h7 : g7 = Perm.one 120 :=
    aut_fix_trivial hg7 (hf7 0 (by decide)).2 (hf7 1 (by decide)).2 (hf7 2 (by decide)).2
      (hf7 4 (by decide)).2 (hf7 6 (by decide)).2 (hf7 8 (by decide)).2
      (hf7 10 (by decide)).2
  rw [he0, he1, he2, he3, he4, he5, he6, h7]
  exact Perm.Gen.comp_mem ht0 (Perm.Gen.comp_mem ht1 (Perm.Gen.comp_mem ht2
    (Perm.Gen.comp_mem ht3 (Perm.Gen.comp_mem ht4 (Perm.Gen.comp_mem ht5
      (Perm.Gen.comp_mem ht6 Perm.Gen.one))))))

/-- `|P| = N`: a duplicate-free list of exactly the permutations satisfying
`P`. This is `HasOrder` for a subgroup given by a membership predicate rather
than by generators. -/
@[expose] public def HasOrderP (P : Perm 120 → Prop) (N : Nat) : Prop :=
  ∃ L : List (Perm 120), L.Nodup ∧ (∀ g : Perm 120, g ∈ L ↔ P g) ∧ L.length = N

/-- **The gauge group of the witness AtlasInstance has `4608` elements.** The
count is the stabiliser chain of `stabChain`, which is a Schreier-Sims run on
the stabiliser subgroup and does not use `T28`'s number; that the group the
chain counts is the whole gauge group is `gauge_eq`.

This is not `T29`, and not `T49`: both are stated in the document for every
AtlasInstance, and carrying this count from the witness to another instance is
exactly the transitivity of `Aut` on `Atl` -- the document's `T27` -- which is
not proved here. -/
public theorem gaugeOrderWitness : HasOrderP (D28 (Blocks.V Blocks.A0)) 4608 := by
  obtain ⟨L, hnd, hmem, hlen⟩ := stabOrder
  refine ⟨L, hnd, fun g => ?_, hlen⟩
  rw [hmem g, W0_eq]
  exact (gauge_eq g).symm



/-! ## The block permutation and its kernel

`rho` sends a gauge element to the permutation it induces on the four blocks.
It is defined for every tuple of four sets and every permutation -- the
definition looks each image up and falls back on the identity when the lookup
is not a permutation -- and `D28a_action` is the statement that on the gauge
group of the witness it *is* the action on the blocks. That statement is
proved by induction on the generation of `gauge_eq`'s group: the four
generators permute the four blocks by one kernel check, and permuting them is
closed under products and inverses. -/

/-- The index of `S` among the four sets `bs`, or `3` when it is none of the
first three. -/
@[expose] public def blkOf (bs : Fin 4 → Bitset) (S : Bitset) : Fin 4 :=
  if S = bs 0 then 0 else if S = bs 1 then 1 else if S = bs 2 then 2 else 3

/-- The inverse of a self-map of `Fin 4`, by search. -/
@[expose] public def invOf4 (f : Fin 4 → Fin 4) (i : Fin 4) : Fin 4 :=
  if f 0 = i then 0 else if f 1 = i then 1 else if f 2 = i then 2 else 3

/-- A self-map of `Fin 4` as a permutation, when the search inverts it. -/
@[expose] public def permOf4 (f : Fin 4 → Fin 4) : Perm 4 :=
  if h : (∀ i, invOf4 f (f i) = i) ∧ (∀ i, f (invOf4 f i) = i) then
    ⟨f, invOf4 f, h.1, h.2⟩
  else Perm.one 4

public theorem fin4_cases (j : Fin 4) (h0 : j ≠ 0) (h1 : j ≠ 1) (h2 : j ≠ 2) : j = 3 := by
  have hlt := j.isLt
  have v0 : j.val ≠ 0 := fun hv => h0 (Fin.eq_of_val_eq hv)
  have v1 : j.val ≠ 1 := fun hv => h1 (Fin.eq_of_val_eq hv)
  have v2 : j.val ≠ 2 := fun hv => h2 (Fin.eq_of_val_eq hv)
  exact Fin.eq_of_val_eq (by omega)

/-- The search inverts a permutation, so `permOf4` recovers it. -/
public theorem permOf4_of_perm (s : Perm 4) : permOf4 s.toFun = s := by
  have hright : ∀ i : Fin 4, s.toFun (invOf4 s.toFun i) = i := by
    intro i
    show s.toFun (if s.toFun 0 = i then 0 else if s.toFun 1 = i then 1
      else if s.toFun 2 = i then 2 else 3) = i
    by_cases h0 : s.toFun 0 = i
    · rw [if_pos h0]; exact h0
    · rw [if_neg h0]
      by_cases h1 : s.toFun 1 = i
      · rw [if_pos h1]; exact h1
      · rw [if_neg h1]
        by_cases h2 : s.toFun 2 = i
        · rw [if_pos h2]; exact h2
        · rw [if_neg h2]
          have hj : s.toFun (s.invFun i) = i := s.right_inv i
          have h3 : s.invFun i = 3 :=
            fin4_cases _ (fun he => h0 (by rw [← he]; exact hj))
              (fun he => h1 (by rw [← he]; exact hj)) (fun he => h2 (by rw [← he]; exact hj))
          rw [← h3]; exact hj
  have hleft : ∀ i : Fin 4, invOf4 s.toFun (s.toFun i) = i := by
    intro i
    exact Perm.toFun_injective (hright (s.toFun i))
  rw [permOf4, dif_pos ⟨hleft, hright⟩]
  exact Perm.ext (fun i => rfl)

/-- `D28a`. `rho : Gauge(W) -> Sym(4)`, the action on the four blocks: the
`i`-th block goes to the `rho(g) i`-th. It is packaged as a permutation of the
four block indices rather than as a self-map of `Fin 4`, which is what
`D28a_action` needs in order to state that it *is* the action.

The document notes `rho` is well defined by `T26`, that the four blocks are
determined by `W`. This module makes that dependence explicit rather than
implicit: `rho` is a function of the presentation `bs`, so it exists before
`T26` does, and `T26` upgrades it from "the action on this presentation" to
"the action on `W`'s blocks" instead of being needed to make it well formed. -/
@[expose] public def D28a (bs : Fin 4 → Bitset) (g : Perm 120) : Perm 4 :=
  permOf4 (fun i => blkOf bs (actP g (bs i)))

/-- `D29`. `Ker := ker(rho)`: the gauge elements fixing every block. -/
@[expose] public def D29 (bs : Fin 4 → Bitset) (W : Bitset) (g : Perm 120) : Prop :=
  D28 W g ∧ D28a bs g = Perm.one 4

/-- The block permutation of a packed word. -/
@[expose] public def blkPermT (t : Nat) : Perm 4 :=
  permOf4 (fun i => blkOf Blocks.blkSet (actT t (Blocks.blkSet i)))

set_option maxHeartbeats 1000000 in
/-- Each of the four generators of the gauge group permutes the four blocks.
`blkPermT` falls back on the identity when the lookup is not a permutation, so
this one check carries both halves: the images are blocks, and the induced map
of indices is a permutation. -/
public theorem stabBlkComp : stabGt.all (fun q =>
    allFin (fun i : Fin 4 => decide (actT q.1 (Blocks.blkSet i)
      = Blocks.blkSet ((blkPermT q.1).toFun i)))) = true := by decide +kernel

public theorem blkOf_blkSet : ∀ j : Fin 4, blkOf Blocks.blkSet (Blocks.blkSet j) = j := by
  decide +kernel

public theorem gen_block_perm {s : Perm 120} (hs : s ∈ permsOf stabGt) :
    ∃ t : Perm 4, ∀ i : Fin 4, actP s (Blocks.blkSet i) = Blocks.blkSet (t.toFun i) := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
  refine ⟨blkPermT q.1, fun i => ?_⟩
  rw [show (tpermP q : Perm 120) = tperm q.1 q.2 from rfl, ← actT_eq (stabGt_ok q hq)]
  exact of_decide_eq_true (allFin_true _ (List.all_eq_true.mp stabBlkComp q hq) i)

/-- Every element of the chain's group permutes the four blocks. -/
public theorem gen_blocks {g : Perm 120} (h : Perm.Gen (permsOf stabGt) g) :
    ∃ t : Perm 4, ∀ i : Fin 4, actP g (Blocks.blkSet i) = Blocks.blkSet (t.toFun i) := by
  induction h with
  | one => exact ⟨Perm.one 4, fun i => actP_one (Blocks.blkIsBlock i).1⟩
  | @step p s _ hs ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := gen_block_perm hs
    exact ⟨a.comp b, fun i => by rw [actP_comp, hb i, ha (b.toFun i)]; rfl⟩
  | @stepInv p s _ hs ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := gen_block_perm hs
    refine ⟨a.comp b.inv, fun i => ?_⟩
    have hinv : actP s.inv (Blocks.blkSet i) = Blocks.blkSet (b.invFun i) := by
      have h1 : actP s.inv (actP s (Blocks.blkSet (b.invFun i))) = Blocks.blkSet (b.invFun i) := by
        rw [← actP_comp, Perm.inv_comp]
        exact actP_one (Blocks.blkIsBlock _).1
      rw [hb (b.invFun i), b.right_inv] at h1
      exact h1
    rw [actP_comp, hinv, ha (b.invFun i)]
    rfl

/-- Every gauge element permutes the four blocks of the witness. -/
public theorem gauge_blocks {g : Perm 120} (hg : D28 W0 g) :
    ∃ t : Perm 4, ∀ i : Fin 4, actP g (Blocks.blkSet i) = Blocks.blkSet (t.toFun i) :=
  gen_blocks ((gauge_eq g).mp hg)

/-- **`rho` is the action on the four blocks** on the gauge group of the
witness AtlasInstance. -/
public theorem D28a_action {g : Perm 120} (hg : D28 W0 g) (i : Fin 4) :
    actP g (Blocks.blkSet i) = Blocks.blkSet ((D28a Blocks.blkSet g).toFun i) := by
  obtain ⟨t, ht⟩ := gauge_blocks hg
  have hraw : (fun j => blkOf Blocks.blkSet (actP g (Blocks.blkSet j))) = t.toFun := by
    funext j
    rw [ht j, blkOf_blkSet]
  show actP g (Blocks.blkSet i)
    = Blocks.blkSet ((permOf4 (fun j => blkOf Blocks.blkSet (actP g (Blocks.blkSet j)))).toFun i)
  rw [hraw, permOf4_of_perm]
  exact ht i

/-- `Ker` is the pointwise stabiliser of the four blocks. -/
public theorem D29_iff {g : Perm 120} (hg : D28 W0 g) :
    D29 Blocks.blkSet W0 g ↔ (∀ i : Fin 4, actP g (Blocks.blkSet i) = Blocks.blkSet i) := by
  constructor
  · intro h i
    rw [D28a_action hg i, h.2]
    rfl
  · intro h
    refine ⟨hg, ?_⟩
    have hraw : (fun j => blkOf Blocks.blkSet (actP g (Blocks.blkSet j)))
        = (Perm.one 4).toFun := by
      funext j
      rw [h j, blkOf_blkSet]
      rfl
    show permOf4 (fun j => blkOf Blocks.blkSet (actP g (Blocks.blkSet j))) = Perm.one 4
    rw [hraw, permOf4_of_perm]

/-! ## The categorical layer, instantiated on the orbit of the witness

`UorAtlas.Category` states nineteen theorems over an `AtlasAction`: a subgroup
of `Perm n` acting on a type, a population that is one orbit of the action,
and the order of the stabiliser of a base point. Two of the three are
available here. The group is `Aut`; the stabiliser order is
`gaugeOrderWitness`; the population is the `Aut`-orbit of the witness
AtlasInstance.

That orbit is *not* known to be `Atl`. `Atl subset orbit` is the document's
`T27` and is not proved here, and `orbit subset Atl` needs the blocks of an
image to be blocks, which is the rank clause of `D16` and is not proved here
either. So the nineteen theorems become facts about the category of the orbit,
and they become facts about `Atl` exactly when `T27` is supplied. -/

/-- The objects: class subsets, which is what `actP` acts on. -/
@[expose] public def ClSet : Type := { W : Bitset // Blocks.ClassSet W }

/-- The action data of `D23` for `Aut` acting on the orbit of `W_0`. -/
@[expose] public def orbitData : Category.ActionData 120 where
  Grp := D21
  one_mem := Perm.Gen.one
  comp_mem := fun hg hh => Perm.Gen.comp_mem hg hh
  inv_mem := fun hg => Perm.Gen.inv_mem hg
  Obj := ClSet
  act := fun g W => ⟨actP g W.val, classSet_actP g W.val⟩
  act_one := fun W => Subtype.ext (actP_one W.property)
  act_comp := fun g h W => Subtype.ext (actP_comp g h W.val)
  IsOb := fun W => ∃ g : Perm 120, D21 g ∧ actP g W0 = W.val
  stable := fun {g} hg {W} hW => by
    obtain ⟨h, hh, hhW⟩ := hW
    exact ⟨g.comp h, Perm.Gen.comp_mem hg hh, by
      show actP (g.comp h) W0 = actP g W.val
      rw [actP_comp, hhW]⟩
  base := ⟨W0, classSet_W0⟩
  base_isOb := ⟨Perm.one 120, Perm.Gen.one, actP_one classSet_W0⟩
  transitive := fun {W} hW => by
    obtain ⟨g, hg, hgW⟩ := hW
    exact ⟨g, hg, Subtype.ext hgW⟩

public theorem nodup_pmap {α β : Type} {p : α → Prop} (f : (a : α) → p a → β)
    (hinj : ∀ (a₁ : α) (h₁ : p a₁) (a₂ : α) (h₂ : p a₂), f a₁ h₁ = f a₂ h₂ → a₁ = a₂) :
    ∀ (l : List α) (H : ∀ a ∈ l, p a), l.Nodup → (l.pmap f H).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; exact List.nodup_nil
  | cons a as ih =>
    intro H hnd
    have hnd' := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨?_, ih _ hnd'.2⟩
    intro hmem
    obtain ⟨a', h', he⟩ := List.mem_pmap.mp hmem
    exact hnd'.1 (hinj a' _ a _ he ▸ h')

/-- The stabiliser of the base object, as a type, has `4608` elements. This is
`AtlasAction`'s missing field, and it is `gaugeOrderWitness` transported to the
subtype the categorical layer counts. -/
public theorem orbit_stab_card :
    Category.HasCard (Category.D25 orbitData (Category.Atl.basePt orbitData)) 4608 := by
  obtain ⟨L, hnd, hmem, hlen⟩ := gaugeOrderWitness
  have hP : ∀ g ∈ L, D21 g ∧ actP g W0 = W0 := by
    intro g hg
    have h := (hmem g).mp hg
    rw [W0_eq] at h
    exact h
  have hP' : ∀ g ∈ L, orbitData.Grp g
      ∧ orbitData.act g (Category.Atl.basePt orbitData).val
        = (Category.Atl.basePt orbitData).val :=
    fun g hg => ⟨(hP g hg).1, Subtype.ext (hP g hg).2⟩
  refine ⟨L.pmap (fun g hg => (⟨g, hg⟩ : Category.D25 orbitData
      (Category.Atl.basePt orbitData))) hP', ?_, ?_, ?_⟩
  · exact nodup_pmap _ (fun a₁ h₁ a₂ h₂ he => congrArg Subtype.val he) L hP' hnd
  · intro a
    refine List.mem_pmap.mpr ⟨a.val, ?_, Subtype.ext rfl⟩
    refine (hmem a.val).mpr ?_
    rw [W0_eq]
    exact ⟨a.property.1, congrArg Subtype.val a.property.2⟩
  · rw [List.length_pmap]
    exact hlen

/-- The action of `D23` on the orbit of the witness, with the stabiliser order
the nineteen theorems of `UorAtlas.Category` consume. -/
@[expose] public def orbitAction : Category.AtlasAction 120 where
  toActionData := orbitData
  stab_card := orbit_stab_card


/-! ## `D21a`: the componentwise action on AtlasPresentations

The document's `Stab_Aut(A)` is a stabiliser for *this* action, so the action
has to exist before the stabiliser can be named. `D21a` bundles the two
commuting actions and the stabiliser, as the document does. -/

/-- `Aut` acting componentwise on the blocks of a presentation. This is
well typed only once the images are again blocks, which `actP` alone does not
give; `actPres` is therefore the raw componentwise map on the block tuple, and
`D21a_stab` below is the stabiliser statement that consumes it. -/
@[expose] public def actPres (g : Perm 120) (b : Fin 4 → Bitset) : Fin 4 → Bitset :=
  fun a => actP g (b a)

/-- `Sym(4)` acting by reindexing, `sigma . (B_0,...,B_3) := (B_{sigma^-1(0)},...)`. -/
@[expose] public def reindex (s : Perm 4) (b : Fin 4 → Bitset) : Fin 4 → Bitset :=
  fun a => b (s.invFun a)

/-- `Stab_Aut(A) := { g in Aut : gB_i = B_i for every i }`, the stabiliser of an
AtlasPresentation under the componentwise action. Note this fixes every block
*separately*; `D28` below fixes only the union. -/
@[expose] public def stabPres (b : Fin 4 → Bitset) (g : Perm 120) : Prop :=
  D21 g ∧ ∀ a : Fin 4, actP g (b a) = b a

/-- `D21a`. The componentwise action, the reindexing action, the fact that the
two commute, and the stabiliser of a presentation. The document states all four
under this one label, so this one declaration carries all four. -/
@[expose] public def D21a :
    (Perm 120 → (Fin 4 → Bitset) → (Fin 4 → Bitset))
      × (Perm 4 → (Fin 4 → Bitset) → (Fin 4 → Bitset))
      × ((Fin 4 → Bitset) → Perm 120 → Prop) :=
  (actPres, reindex, stabPres)

/-- The two actions of `D21a` commute, which is the part of `D21a` that is a
claim rather than a definition. -/
public theorem D21a_commute (g : Perm 120) (s : Perm 4) (b : Fin 4 → Bitset) :
    actPres g (reindex s b) = reindex s (actPres g b) := rfl

/-- The componentwise action is an action of `Aut`. -/
public theorem actPres_comp (g h : Perm 120) (b : Fin 4 → Bitset) :
    actPres (g.comp h) b = actPres g (actPres h b) :=
  funext (fun a => actP_comp g h (b a))

/-- A presentation's stabiliser is a subgroup: it contains the identity and is
closed under composition and inverse. -/
public theorem stabPres_subgroup {b : Fin 4 → Bitset} (hb : ∀ a, Blocks.ClassSet (b a)) :
    stabPres b (Perm.one 120)
      ∧ (∀ g h, stabPres b g → stabPres b h → stabPres b (g.comp h))
      ∧ (∀ g, stabPres b g → stabPres b g.inv) := by
  refine ⟨⟨D21_subgroup.2.1, fun a => actP_one (hb a)⟩, ?_, ?_⟩
  · rintro g h ⟨hg, hgs⟩ ⟨hh, hhs⟩
    exact ⟨D21_subgroup.2.2.1 g h hg hh, fun a => by rw [actP_comp, hhs a, hgs a]⟩
  · rintro g ⟨hg, hgs⟩
    refine ⟨D21_subgroup.2.2.2 g hg, fun a => ?_⟩
    have := actP_inv g (hb a)
    rwa [hgs a] at this

/-- Membership in a four-fold union, which `Blocks.union4` does not come with. -/
public theorem mem_union4 (b : Fin 4 → Bitset) (j : Nat) :
    j ∈ Blocks.union4 b ↔ ∃ a : Fin 4, j ∈ b a := by
  rw [Blocks.union4, Bitset.mem_union, Bitset.mem_union, Bitset.mem_union]
  constructor
  · rintro ((h | h) | (h | h))
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  · rintro ⟨a, ha⟩
    match a with
    | 0 => exact Or.inl (Or.inl ha)
    | 1 => exact Or.inl (Or.inr ha)
    | 2 => exact Or.inr (Or.inl ha)
    | 3 => exact Or.inr (Or.inr ha)

/-- Fixing every block fixes their union, so a presentation's stabiliser sits
inside the gauge group of its support. -/
public theorem stabPres_le_D28 {b : Fin 4 → Bitset} {g : Perm 120} (h : stabPres b g) :
    D28 (Blocks.union4 b) g := by
  refine ⟨h.1, Bitset.ext (fun j => ?_)⟩
  rw [mem_actP]
  constructor
  · rintro ⟨i, hi, he⟩
    obtain ⟨a, ha⟩ := (mem_union4 b i.val).mp hi
    refine (mem_union4 b j).mpr ⟨a, ?_⟩
    rw [← h.2 a, mem_actP]
    exact ⟨i, ha, he⟩
  · intro hj
    obtain ⟨a, ha⟩ := (mem_union4 b j).mp hj
    rw [← h.2 a, mem_actP] at ha
    obtain ⟨i, hi, he⟩ := ha
    exact ⟨i, (mem_union4 b i.val).mpr ⟨a, hi⟩, he⟩

/-! ## `D30`: the automorphism group of a single block -/

/-- The `Z`-span of the roots of a block: the integer combinations of roots
whose classes lie in `B`. `D30` quantifies over linear maps *of `span(B)`*, so
the span has to be a predicate before the maps can be. -/
public inductive SpanOf (B : Bitset) : Vec 8 Int → Prop where
  | root {x : Vec 8 Int} : Blocks.RootsOf B x → SpanOf B x
  | zero : SpanOf B (fun _ => 0)
  | add {x y : Vec 8 Int} : SpanOf B x → SpanOf B y → SpanOf B (fun i => x i + y i)
  | neg {x : Vec 8 Int} : SpanOf B x → SpanOf B (AddCommGroup.neg x)

/-- `D30`. For a block `B`, `Aut(B)` is the group of linear maps of `span(B)`
preserving `{ x in R : k(x) in B }`.

"Linear map of `span(B)`" is additivity on `span(B)`; over `Z` that already
forces compatibility with integer scaling, so no separate scalar clause is
needed. "Preserving" is bijectivity on the root set, given here as an explicit
two-sided inverse rather than as surjectivity, because a group is what the
document names and an inverse is what makes it one. -/
@[expose] public def D30 (B : Bitset) (f : Vec 8 Int → Vec 8 Int) : Prop :=
  (∀ x y : Vec 8 Int, SpanOf B x → SpanOf B y →
      f (fun i => x i + y i) = fun i => f x i + f y i)
    ∧ (∀ x : Vec 8 Int, SpanOf B x → SpanOf B (f x))
    ∧ (∀ x : Vec 8 Int, Blocks.RootsOf B x → Blocks.RootsOf B (f x))
    ∧ ∃ g : Vec 8 Int → Vec 8 Int,
        (∀ x : Vec 8 Int, Blocks.RootsOf B x → Blocks.RootsOf B (g x))
          ∧ (∀ x : Vec 8 Int, Blocks.RootsOf B x → g (f x) = x)
          ∧ (∀ x : Vec 8 Int, Blocks.RootsOf B x → f (g x) = x)

/-- `Aut(B)` contains the identity. -/
public theorem D30_id (B : Bitset) : D30 B (fun x => x) :=
  ⟨fun _ _ _ _ => rfl, fun _ h => h, fun _ h => h,
    ⟨fun x => x, fun _ h => h, fun _ _ => rfl, fun _ _ => rfl⟩⟩

/-- `Aut(B)` is closed under composition. -/
public theorem D30_comp {B : Bitset} {f g : Vec 8 Int → Vec 8 Int}
    (hf : D30 B f) (hg : D30 B g) : D30 B (fun x => f (g x)) := by
  obtain ⟨hfa, hfs, hfr, fi, hfi1, hfi2, hfi3⟩ := hf
  obtain ⟨hga, hgs, hgr, gi, hgi1, hgi2, hgi3⟩ := hg
  refine ⟨fun x y hx hy => ?_, fun x hx => hfs _ (hgs x hx), fun x hx => hfr _ (hgr x hx),
    ⟨fun x => gi (fi x), fun x hx => hgi1 _ (hfi1 x hx), fun x hx => ?_, fun x hx => ?_⟩⟩
  · show f (g (fun i => x i + y i)) = _
    rw [hga x y hx hy, hfa _ _ (hgs x hx) (hgs y hy)]
  · show gi (fi (f (g x))) = x
    rw [hfi2 _ (hgr x hx), hgi2 x hx]
  · show f (g (gi (fi x))) = x
    rw [hgi3 _ (hfi1 x hx), hfi3 x hx]

/-- `-1` is an automorphism of every block: negation is additive, and the root
set of a block is closed under negation because `K` is a quotient by sign. -/
public theorem D30_neg (B : Bitset) : D30 B (fun x => AddCommGroup.neg x) := by
  have hroot : ∀ x : Vec 8 Int, Blocks.RootsOf B x → Blocks.RootsOf B (AddCommGroup.neg x) := by
    rintro x ⟨hx, hc⟩
    exact ⟨D11_neg hx, by rw [D12_of_nrm (nrm_neg hx)]; exact hc⟩
  have hadd : ∀ x y : Vec 8 Int, (AddCommGroup.neg (fun i => x i + y i) : Vec 8 Int)
      = fun i => AddCommGroup.neg x i + AddCommGroup.neg y i :=
    fun x y => funext (fun i => by show -(x i + y i) = -(x i) + -(y i); omega)
  refine ⟨fun x y _ _ => hadd x y, fun x hx => SpanOf.neg hx, hroot,
    ⟨fun x => AddCommGroup.neg x, hroot, fun x _ => vneg_neg x, fun x _ => vneg_neg x⟩⟩


/-! ## `V68b`: `-I` is in `WLin` and in the kernel of `pi` -/

/-- The reflection is odd: the coefficient it subtracts is linear because the
division is exact on `L`. -/
public theorem D20vec_neg (a : Fin 8) {x : Vec 8 Int} (h : (4 : Int) ∣ dot x (D19a a)) :
    D20vec a (AddCommGroup.neg x) = AddCommGroup.neg (D20vec a x) := by
  obtain ⟨c, hc⟩ := h
  funext m
  have hl : D20vec a (AddCommGroup.neg x) m = (AddCommGroup.neg x : Vec 8 Int) m - (dot (AddCommGroup.neg x) (D19a a) / 4) * D19a a m :=
    rfl
  have hr : (AddCommGroup.neg (D20vec a x) : Vec 8 Int) m = -(x m - (dot x (D19a a) / 4) * D19a a m) := rfl
  rw [hl, hr, dot_neg_left, hc, show ((AddCommGroup.neg x : Vec 8 Int) m) = -(x m) from rfl,
    show (-(4 * c)) = 4 * (-c) from by omega, Int.mul_ediv_cancel_left _ (by decide),
    Int.mul_ediv_cancel_left _ (by decide)]
  grind

public theorem D20vec_rep_cases (a : Fin 8) {i : Nat} (hi : i < 120) :
    D20vec a (repN i) = repN (D20idx a i) ∨ D20vec a (repN i) = AddCommGroup.neg (repN (D20idx a i)) := by
  have hroot : D11 (repN i) := D11_rep ⟨i, hi⟩
  have himg : D11 (D20vec a (repN i)) := (V66b a).1 _ hroot
  have hrep : rep (D12 (D20vec a (repN i))) = nrm (D20vec a (repN i)) := rep_D12 himg
  have hidx : repN (D20idx a i) = rep (D12 (D20vec a (repN i))) := rfl
  rw [hidx, hrep, nrm]
  by_cases hp : 0 < dot (D20vec a (repN i)) posRef
  · exact Or.inl (by rw [if_pos hp])
  · refine Or.inr ?_
    rw [if_neg hp]
    exact (vneg_neg _).symm

public theorem dvd_dot_repN (a : Fin 8) {i : Nat} (hi : i < 120) :
    (4 : Int) ∣ dot (repN i) (D19a a) := by
  have h := (V66comp_at ⟨i, by omega⟩ a).2.2
  rw [show R240 ⟨i, by omega⟩ = repN i from by
    show (if i < 120 then repN i else AddCommGroup.neg (repN (i - 120))) = repN i
    rw [if_pos hi]] at h
  exact Int.dvd_of_emod_eq_zero h

/-- The reflections of a word, applied to a vector: the head acts last, which
is the order in which the matrices below multiply. -/
@[expose] public def D20fold : List (Fin 8) → Vec 8 Int → Vec 8 Int
  | [], x => x
  | j :: w, x => D20vec j (D20fold w x)

public theorem D20fold_root : ∀ (w : List (Fin 8)) {x : Vec 8 Int}, D11 x → D11 (D20fold w x) := by
  intro w
  induction w with
  | nil => intro x h; exact h
  | cons j w ih => intro x h; exact (V66b j).1 _ (ih h)

/-- The state of the sign fold: a class index and a sign. -/
@[expose] public def stVec (st : Nat × Bool) : Vec 8 Int :=
  match st.2 with
  | true => repN st.1
  | false => AddCommGroup.neg (repN st.1)

/-- One step of the sign fold: the class moves by `D20idx`, and the sign flips
exactly when the reflected representative is the negative of the target
class's representative. -/
@[expose] public def signStep (a : Fin 8) (st : Nat × Bool) : Nat × Bool :=
  (D20idx a st.1,
    match vecEq8 (D20vec a (repN st.1)) (repN (D20idx a st.1)) with
    | true => st.2
    | false => Bool.not st.2)

/-- The sign fold of a word. Its class component is the packed permutation of
`D20`; its sign component is the one bit that tells `-I` from `I`, and it is
what no computation on classes alone can see. -/
@[expose] public def foldSign : List (Fin 8) → Nat × Bool → Nat × Bool
  | [], st => st
  | j :: w, st => signStep j (foldSign w st)

public theorem stVec_true {st : Nat × Bool} (h : st.2 = true) : stVec st = repN st.1 := by
  show (match st.2 with | true => repN st.1 | false => AddCommGroup.neg (repN st.1)) = _
  rw [h]

public theorem stVec_false {st : Nat × Bool} (h : st.2 = false) :
    stVec st = AddCommGroup.neg (repN st.1) := by
  show (match st.2 with | true => repN st.1 | false => AddCommGroup.neg (repN st.1)) = _
  rw [h]

public theorem signStep_spec (j : Fin 8) (st : Nat × Bool) (h : st.1 < 120) :
    D20vec j (stVec st) = stVec (signStep j st) := by
  have hfst : (signStep j st).1 = D20idx j st.1 := rfl
  cases hv : vecEq8 (D20vec j (repN st.1)) (repN (D20idx j st.1)) with
  | true =>
    have hpos : D20vec j (repN st.1) = repN (D20idx j st.1) := vecEq8_eq hv
    have hsnd : (signStep j st).2 = st.2 := by
      show (match vecEq8 (D20vec j (repN st.1)) (repN (D20idx j st.1)) with
        | true => st.2 | false => Bool.not st.2) = st.2
      rw [hv]
    cases hs : st.2 with
    | true => rw [stVec_true hs, stVec_true (by rw [hsnd, hs]), hfst, hpos]
    | false =>
      rw [stVec_false hs, stVec_false (by rw [hsnd, hs]), hfst,
        D20vec_neg j (dvd_dot_repN j h), hpos]
  | false =>
    have hneg : D20vec j (repN st.1) = AddCommGroup.neg (repN (D20idx j st.1)) := by
      rcases D20vec_rep_cases j h with hc | hc
      · exact absurd (show vecEq8 (D20vec j (repN st.1)) (repN (D20idx j st.1)) = true by
          rw [hc]; exact allFin_of _ (fun m => decide_eq_true rfl))
          (by rw [hv]; exact Bool.noConfusion)
      · exact hc
    have hsnd : (signStep j st).2 = Bool.not st.2 := by
      show (match vecEq8 (D20vec j (repN st.1)) (repN (D20idx j st.1)) with
        | true => st.2 | false => Bool.not st.2) = Bool.not st.2
      rw [hv]
    cases hs : st.2 with
    | true => rw [stVec_true hs, stVec_false (by rw [hsnd, hs]; rfl), hfst, hneg]
    | false =>
      rw [stVec_false hs, stVec_true (by rw [hsnd, hs]; rfl), hfst,
        D20vec_neg j (dvd_dot_repN j h), hneg, vneg_neg]

public theorem foldSign_spec : ∀ (w : List (Fin 8)) (st : Nat × Bool), st.1 < 120 →
    (foldSign w st).1 < 120 ∧ D20fold w (stVec st) = stVec (foldSign w st) := by
  intro w
  induction w with
  | nil => intro st h; exact ⟨h, rfl⟩
  | cons j w ih =>
    intro st h
    obtain ⟨hlt, heq⟩ := ih st h
    refine ⟨(D12 (D20vec j (repN (foldSign w st).1))).isLt, ?_⟩
    show D20vec j (D20fold w (stVec st)) = stVec (signStep j (foldSign w st))
    rw [heq]
    exact signStep_spec j (foldSign w st) hlt

/-! ### The word, and the matrix it evaluates to

`(r_1 r_2 ... r_8)^15` is the Coxeter element of `E_8` to the power `h/2`, and
that is the longest element of the Weyl group, which is `-1`. The certificate
below runs the sign fold on the eight classes of the simple roots: each comes
back to itself with the sign reversed, which is exactly `r(a_j) = -a_j` for
every `j`, and a matrix that negates a basis is `-I`. -/

/-- `(r_1 r_2 ... r_8)^15`. -/
@[expose] public def negWord : List (Fin 8) := (List.replicate 15 (List.finRange 8)).flatten

set_option maxHeartbeats 4000000 in
/-- The word returns the class of each simple root to itself, with the sign
reversed. -/
public theorem negWordComp : allFin (fun j : Fin 8 =>
    Nat.beq (foldSign negWord ((D12 (D19a j)).val, true)).1 (D12 (D19a j)).val
      && Bool.not (foldSign negWord ((D12 (D19a j)).val, true)).2) = true := by decide +kernel

/-- The matrix of a word, in the coordinates of the `V65c` basis. -/
@[expose] public def matWord : List (Fin 8) → Mat 8 8 Int
  | [] => Mat.id
  | j :: w => Mat.mul (Places.reflMat j) (matWord w)

public theorem wlin_matWord : ∀ w : List (Fin 8), Places.WLinMem (matWord w) := by
  intro w
  induction w with
  | nil => exact Places.WLinMem.one
  | cons j w ih => exact Places.WLinMem.mul (Places.WLinMem.gen j) ih

/-- The bridge check for one simple root: `D41`'s reflection and `D20`'s are
the same map of the lattice. One is written in the coordinates of the `V65c`
basis and the other in the coordinates of section `0`, and this is the only
place the two presentations of `r_a` meet.

It is eight declarations rather than one because the kernel releases memory
between declarations and not inside a single `decide`: `reflOn` reads the
`Sim` coordinates of its argument, which is a matrix apply against `gramInv`,
and `1920` of those in one certificate cost three and a half gigabytes where
eight certificates of `240` cost half of one. -/
@[expose] public def reflOnChk (j : Fin 8) : Bool :=
  allFin (fun i : Fin 240 => vecEq8 (Places.reflOn j (R240 i)) (D20vec j (R240 i)))

set_option maxHeartbeats 4000000 in
public theorem reflOnChk0 : reflOnChk 0 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem reflOnChk1 : reflOnChk 1 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem reflOnChk2 : reflOnChk 2 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem reflOnChk3 : reflOnChk 3 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem reflOnChk4 : reflOnChk 4 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem reflOnChk5 : reflOnChk 5 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem reflOnChk6 : reflOnChk 6 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem reflOnChk7 : reflOnChk 7 = true := by decide +kernel

public theorem reflOnComp : ∀ j : Fin 8, reflOnChk j = true
  | ⟨0, _⟩ => reflOnChk0
  | ⟨1, _⟩ => reflOnChk1
  | ⟨2, _⟩ => reflOnChk2
  | ⟨3, _⟩ => reflOnChk3
  | ⟨4, _⟩ => reflOnChk4
  | ⟨5, _⟩ => reflOnChk5
  | ⟨6, _⟩ => reflOnChk6
  | ⟨7, _⟩ => reflOnChk7

public theorem reflOn_eq (j : Fin 8) {x : Vec 8 Int} (hx : D11 x) :
    Places.reflOn j x = D20vec j x := by
  obtain ⟨i, hi⟩ := T5.2.2 x hx
  rw [hi]
  exact vecEq8_eq (allFin_true _ (reflOnComp j) i)

public theorem emb_reflMat (j : Fin 8) (c : Vec 8 Int) (h : D11 (Places.emb c)) :
    Places.emb (Mat.apply (Places.reflMat j) c) = D20vec j (Places.emb c) := by
  have hsc : Places.simCoord (Places.emb c) = c :=
    Places.emb_inj (Places.emb_recon (Places.emb_memL c))
  have h1 : Places.reflOn j (Places.emb c) = Places.emb (Places.reflCoord j c) := by
    show Places.emb (Places.reflCoord j (Places.simCoord (Places.emb c))) = _
    rw [hsc]
  rw [← Places.reflCoord_eq, ← h1, reflOn_eq j h]

public theorem emb_matWord : ∀ (w : List (Fin 8)) (c : Vec 8 Int), D11 (Places.emb c) →
    Places.emb (Mat.apply (matWord w) c) = D20fold w (Places.emb c) := by
  intro w
  induction w with
  | nil =>
    intro c _
    show Places.emb (Mat.apply Mat.id c) = _
    rw [Mat.apply_id]
    rfl
  | cons j w ih =>
    intro c h
    show Places.emb (Mat.apply (Mat.mul (Places.reflMat j) (matWord w)) c)
      = D20vec j (D20fold w (Places.emb c))
    rw [Mat.apply_mul, emb_reflMat j _ (by rw [ih c h]; exact D20fold_root w h), ih c h]

/-! ### `V68b` -/

public theorem dvd_dot_root {x : Vec 8 Int} (hx : D11 x) (a : Fin 8) :
    (4 : Int) ∣ dot x (D19a a) := by
  obtain ⟨i, hi⟩ := T5.2.2 x hx
  rw [hi]
  exact Int.dvd_of_emod_eq_zero (V66comp_at i a).2.2

/-- The fold is odd, because each reflection is. -/
public theorem D20fold_neg : ∀ (w : List (Fin 8)) {x : Vec 8 Int}, D11 x →
    D20fold w (AddCommGroup.neg x) = AddCommGroup.neg (D20fold w x) := by
  intro w
  induction w with
  | nil => intro x _; rfl
  | cons j w ih =>
    intro x hx
    show D20vec j (D20fold w (AddCommGroup.neg x)) = AddCommGroup.neg (D20vec j (D20fold w x))
    rw [ih hx, D20vec_neg j (dvd_dot_root (D20fold_root w hx) j)]

/-- The fold of the word negates every simple root. -/
public theorem D20fold_simple (j : Fin 8) : D20fold negWord (D19a j) = AddCommGroup.neg (D19a j) := by
  have hroot : D11 (D19a j) := V65a.1 j
  have hk : (D12 (D19a j)).val < 120 := (D12 (D19a j)).isLt
  have hcomp := allFin_true _ negWordComp j
  rw [Bool.and_eq_true] at hcomp
  have hidx : (foldSign negWord ((D12 (D19a j)).val, true)).1 = (D12 (D19a j)).val :=
    Nat.eq_of_beq_eq_true hcomp.1
  have hsgn : (foldSign negWord ((D12 (D19a j)).val, true)).2 = false := by
    cases hs : (foldSign negWord ((D12 (D19a j)).val, true)).2 with
    | true => rw [hs] at hcomp; exact absurd hcomp.2 (by decide)
    | false => rfl
  have hfold : D20fold negWord (rep (D12 (D19a j))) = AddCommGroup.neg (rep (D12 (D19a j))) := by
    have h := (foldSign_spec negWord ((D12 (D19a j)).val, true) hk).2
    rw [show stVec ((D12 (D19a j)).val, true) = rep (D12 (D19a j)) from rfl,
      stVec_false hsgn, hidx] at h
    exact h
  rcases dot_sign hroot with hs | hs
  · have hr : rep (D12 (D19a j)) = D19a j := by
      rw [rep_D12 hroot, nrm, if_pos hs]
    rw [← hr, hfold]
  · have hr : rep (D12 (D19a j)) = AddCommGroup.neg (D19a j) := by
      rw [rep_D12 hroot, nrm, if_neg (by omega : ¬ 0 < dot (D19a j) posRef)]
    have h2 : D20fold negWord (AddCommGroup.neg (rep (D12 (D19a j)))) = AddCommGroup.neg (AddCommGroup.neg (rep (D12 (D19a j)))) := by
      rw [D20fold_neg negWord (D11_rep _), hfold]
    have h3 : AddCommGroup.neg (rep (D12 (D19a j))) = D19a j := by rw [hr, vneg_neg]
    rw [h3] at h2
    exact h2

/-- The value of `negWord`. -/
@[expose] public def negMat : Mat 8 8 Int := matWord negWord

public theorem negMat_eq : negMat = Mat.neg (Mat.id : Mat 8 8 Int) := by
  funext m j
  have hemb : Places.emb (Mat.apply negMat (Places.simZ j)) = AddCommGroup.neg (D19a j) := by
    show Places.emb (Mat.apply (matWord negWord) (Places.simZ j)) = _
    rw [emb_matWord negWord (Places.simZ j) (by rw [Places.emb_simZ]; exact V65a.1 j),
      Places.emb_simZ]
    exact D20fold_simple j
  have hvec : Mat.apply negMat (Places.simZ j) = AddCommGroup.neg (Places.simZ j) := by
    refine Places.emb_inj ?_
    rw [hemb, Places.emb_neg, Places.emb_simZ]
  have h1 : Mat.apply negMat (Places.simZ j) m = negMat m j := Places.apply_simZ negMat j m
  rw [hvec] at h1
  show negMat m j = -(if m = j then 1 else 0)
  rw [← h1]
  show (AddCommGroup.neg (Places.simZ j) : Vec 8 Int) m = _
  rfl

public theorem apply_neg_id (c : Vec 8 Int) :
    Mat.apply (Mat.neg (Mat.id : Mat 8 8 Int)) c = AddCommGroup.neg c := by
  funext m
  have hstep : ∀ i : Fin 8, CommRing.mul ((Mat.neg (Mat.id : Mat 8 8 Int)) m i) (c i)
      = AddCommGroup.neg (CommRing.mul ((Mat.id : Mat 8 8 Int) m i) (c i)) := by
    intro i
    show CommRing.mul (AddCommGroup.neg ((Mat.id : Mat 8 8 Int) m i)) (c i) = _
    exact Linear.neg_mul _ _
  show Vec.sum (fun i => CommRing.mul ((Mat.neg (Mat.id : Mat 8 8 Int)) m i) (c i)) = _
  rw [Vec.sum_congr hstep, Vec.sum_neg]
  show AddCommGroup.neg (Mat.apply (Mat.id : Mat 8 8 Int) c m) = _
  rw [Mat.apply_id]
  rfl

/-- `V68b`. **`-I` lies in `WLin`, and it lies in the kernel of `pi`.** -/
public theorem V68b : Places.WLinMem (Mat.neg (Mat.id : Mat 8 8 Int))
    ∧ ∀ k : K, Places.D42 (Mat.neg (Mat.id : Mat 8 8 Int)) k = k := by
  refine ⟨negMat_eq ▸ wlin_matWord negWord, fun k => ?_⟩
  show Places.kOf (Mat.apply (Mat.neg (Mat.id : Mat 8 8 Int)) (Places.coordOf k)) = k
  rw [apply_neg_id, Places.kOf_neg (Places.rootC_coordOf k)]
  exact Places.kOf_coordOf k


end UorAtlas.Group
