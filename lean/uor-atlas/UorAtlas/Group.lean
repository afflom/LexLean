module
public import Init
public import UorAtlas.Prelude.Algebra
public import UorAtlas.Prelude.Linear
public import UorAtlas.Prelude.Perm
public import UorAtlas.Roots

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

end UorAtlas.Group
