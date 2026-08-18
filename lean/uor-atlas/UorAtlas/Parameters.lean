module
public import Init

/-!
Section 1 of UOR-ATLAS-FORMAL-001: the parameters.

Every count the rest of the document works with -- `8` coordinates, `24`
classes to a block, `48` to an AtlasInstance, `12288` -- is fixed here, and
fixed *by minimisation*. `D2` is the least admissible dimension; it is not the
numeral `8`. That distinction is the entire content of `T1`: defining `O := 8`
would make `T1` a tautology and would quietly drop the document's claim that
dimension eight is forced by `D1`. So `D2` performs an honest unbounded search
over the decidable predicate `D1`, and `T1` is the theorem that the search
halts at `8`.

`D3` is held to the same standard. `T` is `Nat.log2 O`, the ordinary floor
base-two logarithm, and `2 ^ Nat.log2 n = n` is false for every `n` that is not
a power of two -- `Nat.log2 5 = 2`. The second conjunct of `T2` is therefore a
fact about `O`, not a definitional artifact.

The prelude carries no `Nat.find`, and this library depends on nothing outside
the prelude, so the minimisation is built here from `WellFounded.fix`. It is
local machinery: stated for an arbitrary decidable predicate on `Nat`, kept in
this module because section 1 is the only place the document minimises.
-/

set_option autoImplicit false

namespace UorAtlas.Parameters

/-! ## Minimisation of a decidable predicate

`D2` is a minimum over a predicate on `Nat`, so a minimum has to exist as a
construction before `D2` can name one. `Step p` is the upward search step, well
founded exactly because `p` has a witness; `least` runs the search from `0` and
reads off the first index at which it stops. -/

/-- The upward search step. `Step p n m` holds when the search may advance from
`m` to `n = m + 1`, which it may exactly when `p` has already been refuted at
every index up to and including `m`. -/
@[expose] public def Step (p : Nat → Prop) (n m : Nat) : Prop :=
  n = m + 1 ∧ ∀ k, k ≤ m → ¬ p k

/-- A witness bounds the search: no step is possible past a witness of `p`,
because a step carries the refutation of `p` everywhere below it. Hence the
search relation is well founded and the recursion in `findX` terminates. -/
public theorem stepWf {p : Nat → Prop} (h : ∃ n, p n) : WellFounded (Step p) := by
  refine ⟨fun k => ?_⟩
  cases h with
  | intro w hw =>
    have key : ∀ m k, w ≤ k + m → Acc (Step p) k := by
      intro m
      induction m with
      | zero =>
        intro k hk
        exact Acc.intro k fun _ hy => absurd hw (hy.2 w (by omega))
      | succ m ih =>
        intro k hk
        refine Acc.intro k fun y hy => ?_
        have hyk : y = k + 1 := hy.1
        subst hyk
        exact ih (k + 1) (by omega)
    exact key w k (by omega)

/-- The least index satisfying `p`, packaged with the two properties that make
it least. The recursion starts at `0` and advances one index at a time, and it
carries as an invariant the refutation of `p` at every smaller index, which is
what turns the halting index into a minimum. -/
@[expose] public def findX {p : Nat → Prop} [DecidablePred p] (h : ∃ n, p n) :
    { n : Nat // p n ∧ ∀ m, m < n → ¬ p m } :=
  (stepWf h).fix
    (C := fun k => (∀ m, m < k → ¬ p m) → { n : Nat // p n ∧ ∀ m, m < n → ¬ p m })
    (fun k ih hbelow =>
      if hk : p k then ⟨k, hk, hbelow⟩
      else
        have hle : ∀ j, j ≤ k → ¬ p j := fun j hj hpj =>
          (Nat.eq_or_lt_of_le hj).elim (fun he => hk (he ▸ hpj)) (fun hlt => hbelow j hlt hpj)
        ih (k + 1) ⟨rfl, hle⟩ fun m hm => hle m (Nat.le_of_lt_succ hm))
    0 fun m hm => absurd hm (Nat.not_lt_zero m)

/-- `least h` is the smallest natural number satisfying `p`. -/
@[expose] public def least {p : Nat → Prop} [DecidablePred p] (h : ∃ n, p n) : Nat :=
  (findX h).val

/-- The minimum satisfies the predicate it minimises. -/
public theorem least_holds {p : Nat → Prop} [DecidablePred p] (h : ∃ n, p n) :
    p (least h) :=
  (findX h).property.1

/-- Nothing below the minimum satisfies the predicate. -/
public theorem least_min {p : Nat → Prop} [DecidablePred p] (h : ∃ n, p n)
    {m : Nat} (hm : m < least h) : ¬ p m :=
  (findX h).property.2 m hm

/-- The minimum is a lower bound on the whole set, which with `least_holds` is
the defining property of `min`. -/
public theorem least_le {p : Nat → Prop} [DecidablePred p] (h : ∃ n, p n)
    {n : Nat} (hn : p n) : least h ≤ n :=
  Nat.not_lt.mp fun hlt => least_min h hlt hn

/-! ## The parameters -/

/-- `D1`. `admissible(n) := n > 0 and n = 0 (mod 8)`. -/
@[expose] public def D1 (n : Nat) : Prop := n > 0 ∧ n % 8 = 0

public instance instDecidableD1 (n : Nat) : Decidable (D1 n) :=
  inferInstanceAs (Decidable (n > 0 ∧ n % 8 = 0))

/-- Eight is admissible, so the minimisation defining `D2` has something to
find. -/
public theorem D1_eight : D1 8 := by decide

/-- No dimension below eight is admissible. This is the half of `T1` that the
minimisation cannot supply on its own, and the reason `T1` says something. -/
public theorem D1_lt_eight : ∀ n, n < 8 → ¬ D1 n := by decide

/-- `admissible` is inhabited: the set `D2` minimises over is nonempty. -/
public theorem D1_exists : ∃ n, D1 n := ⟨8, D1_eight⟩

/-- `D2`. `O := min { n : admissible(n) }`. -/
@[expose] public def D2 : Nat := least D1_exists

/-- `D2` is admissible. -/
public theorem D2_admissible : D1 D2 := least_holds D1_exists

/-- `D2` is a lower bound for admissibility, so `D2` really is the minimum of
`D1` and not merely some admissible dimension. -/
public theorem D2_least {n : Nat} (hn : D1 n) : D2 ≤ n := least_le D1_exists hn

/-- `T1`. `O = 8`. -/
public theorem T1 : D2 = 8 :=
  Nat.le_antisymm (D2_least D1_eight)
    (Nat.not_lt.mp fun hlt => D1_lt_eight D2 hlt D2_admissible)

/-- `D3`. `T := log_2 O`. -/
@[expose] public def D3 : Nat := Nat.log2 D2

/-- `T2`. `T = 3` and `2^T = O`. -/
public theorem T2 : D3 = 3 ∧ 2 ^ D3 = D2 := by
  constructor
  · show Nat.log2 D2 = 3
    rw [T1]; rfl
  · show 2 ^ Nat.log2 D2 = D2
    rw [T1]; rfl

/-- `D4`. `stride := T * O`. -/
@[expose] public def D4 : Nat := D3 * D2

/-- `D5`. `scope := 2^(O - 2T)`. -/
@[expose] public def D5 : Nat := 2 ^ (D2 - 2 * D3)

/-- `D6`. `classes := scope * stride`. -/
@[expose] public def D6 : Nat := D5 * D4

/-- `D7`. `context := 2^(O - 1)`. -/
@[expose] public def D7 : Nat := 2 ^ (D2 - 1)

/-- `D8`. `belt := classes * context`. -/
@[expose] public def D8 : Nat := D6 * D7

/-! ### The values

`T3` and `T4` both need the derived parameters evaluated, and each evaluation
consumes the previous one exactly as `D4`-`D8` chain. They are recorded once,
here, rather than twice inside the two theorems. -/

public theorem D4_value : D4 = 24 := by
  show D3 * D2 = 24
  rw [T2.left, T1]

public theorem D5_value : D5 = 4 := by
  show 2 ^ (D2 - 2 * D3) = 4
  rw [T2.left, T1]

public theorem D6_value : D6 = 96 := by
  show D5 * D4 = 96
  rw [D4_value, D5_value]

public theorem D7_value : D7 = 128 := by
  show 2 ^ (D2 - 1) = 128
  rw [T1]

public theorem D8_value : D8 = 12288 := by
  show D6 * D7 = 12288
  rw [D6_value, D7_value]

/-- `T3`. `(stride, scope, classes, context, belt) = (24, 4, 96, 128, 12288)`. -/
public theorem T3 : (D4, D5, D6, D7, D8) = (24, 4, 96, 128, 12288) := by
  rw [D4_value, D5_value, D6_value, D7_value, D8_value]

/-- `T4`. `belt = classes * context = (classes / 2) * (2 * context)`.

The first equality is `D8` read back; the second is the halving that makes an
AtlasInstance `classes / 2 = 48` classes carry twice the context, and it is the
one with content. -/
public theorem T4 : D8 = D6 * D7 ∧ D8 = D6 / 2 * (2 * D7) :=
  ⟨rfl, by rw [D8_value, D6_value, D7_value]⟩

/-- `T30`. `4608 = 2^9 * 3^2`. -/
public theorem T30 : 4608 = 2 ^ 9 * 3 ^ 2 := by decide

end UorAtlas.Parameters
