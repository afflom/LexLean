module
public import Init
public import UorAtlas.Prelude.Linear
public import UorAtlas.Glue

/-!
Section 2 of `UOR-ATLAS-FORMAL-001`: the ambient root system `D9`-`D11`, its
class set `D12`, the class graph `D13`, and the simple system `D19a`.

## Coordinates

Everything below is in the **2x integer scaling** of section 2.6 of the release
plan. A point of `L` has coordinates in `(1/2)Z`; writing `y = 2x` clears the
denominator, so `y` ranges over `Z^O` and

* `<x,x> = 2` reads as `<y,y> = 8`,
* `|<u,v>| = 1` reads as `|<y,z>| = 4`,
* `D9`'s `D` becomes the all-even vectors of coordinate sum `= 0 (mod 4)`,
* the glue vector `(1/2, ..., 1/2)` becomes `(1, ..., 1)`.

`Rat` therefore never appears: every statement here is exact integer
arithmetic, which is what `S32` and `D56` require of the spectral argument.
The single place where the scaling is visible in a *value* is `T58x`, whose
Gram matrix is the document's, not the scaled one; `gram` divides the scaled
form by `4` and `gram_exact` certifies that the division is exact.

## Why this encoding

The kernel replays every computation below, so the encoding is chosen for
kernel reduction rather than for elegance.

* Class data lives in **one `Nat` literal**, `repTable`, four bits per
  coordinate and thirty-two bits per class. `Nat.shiftRight` and `Nat.land` are
  GMP-accelerated in the kernel, so a coordinate lookup is two machine
  operations instead of a walk down a list spine, and the whole table is one
  cached value rather than 120 separate definitions.
* Bounded quantification goes through `allLt`/`allFin`, defined by `Nat.rec`
  and structural recursion. The `Decidable` instance the `decide` tactic would
  otherwise pick for `∀ i : Fin n, p i` is `Nat.decidableBallLT`, which is
  quadratic under kernel reduction; at `n = 6561` it does not terminate in any
  usable time, while `allLt` is linear.
* The `120 x 120` product needed for `T8` is **not** evaluated entry by entry.
  Each adjacency row is packed into a single `Nat` in base `2^16` (`pk`), so
  one row of `A^2` is `120` GMP additions of `1920`-bit integers rather than
  `120^2` scalar multiply-adds. `pk_digit` proves the packing is faithful --
  digit-bounded vectors are recovered from their packed form -- so this is a
  change of representation, not a change of statement. The whole of `T8` is
  therefore `120^2` kernel operations, not `120^3`.
* `T9a` is **derived** from `T7` and `T8` rather than computed: the strongly
  regular identity `A^2 = 24J + 4A + 32I` and row sum `56` give the
  annihilating polynomial by matrix algebra. Computing a second `120 x 120`
  product would have cost as much again as `T8` and proved nothing new.

## The `D19a` witness is constructed here, not transcribed

`D19a` names "the eight vectors listed in `atlas.py`, `SIMPLE`". That file is
not available to this repository, so `D19a` below is an **explicit simple
system constructed here** -- the standard `E8` simple roots -- and *not* a
transcription of the document's witness.

This is sound, and the document says why. `T22`-`T27` establish that the
block, BlockFrame and AtlasInstance populations are single `Aut`-orbits, and
section 20.2a records the general principle: an `Aut`-invariant property
verified on one orbit representative holds on the whole orbit. `V65a`, `V65b`
and `T58x` are statements about *a* simple system -- eight roots of norm `2`,
of full rank, with connected nonorthogonality graph and unimodular Gram matrix
-- and every simple system of `L` is carried to every other by `Aut`. Any
valid witness therefore discharges them, and the one below is proved valid
rather than assumed to be.

## Local machinery

`allLt`, `allFin`, `sumN`, `pk` and `det` are local to this module. Other
modules of the vendored library are concurrently adding permutation, bitset
and ring-lemma preludes; nothing here depends on them.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace UorAtlas.Roots

open UorAtlas.Prelude
open UorAtlas.Prelude.Linear
open UorAtlas.Prelude.AddCommGroup

/-! ## Bounded quantification the kernel can run

`decide` on `∀ i : Fin n, p i` goes through `Nat.decidableBallLT`, whose
kernel reduction is quadratic; these two are linear and structural. -/
/-! ## Bounded quantification that the kernel can run -/

@[expose] public def allLt (f : Nat → Bool) (m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => f k && ih) m

public theorem allLt_succ (f : Nat → Bool) (m : Nat) :
    allLt f (m + 1) = (f m && allLt f m) := rfl

public theorem allLt_true : ∀ (f : Nat → Bool) (m : Nat), allLt f m = true →
    ∀ k, k < m → f k = true := by
  intro f m
  induction m with
  | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro h k hk
    rw [allLt_succ, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge k n with h1 | h1
    · exact ih h.2 k h1
    · exact (Nat.le_antisymm (Nat.le_of_lt_succ hk) h1) ▸ h.1

@[expose] public def allFin : {n : Nat} → (Fin n → Bool) → Bool
  | 0, _ => true
  | _ + 1, f => f 0 && allFin (fun i => f i.succ)

public theorem allFin_succ {n : Nat} (f : Fin (n + 1) → Bool) :
    allFin f = (f 0 && allFin (fun i => f i.succ)) := rfl

public theorem allFin_true : ∀ {n : Nat} (f : Fin n → Bool), allFin f = true →
    ∀ i : Fin n, f i = true := by
  intro n
  induction n with
  | zero => intro _ _ i; exact i.elim0
  | succ k ih =>
    intro f h i
    rw [allFin_succ, Bool.and_eq_true] at h
    refine Fin.cases ?_ ?_ i
    · exact h.1
    · intro i'; exact ih (fun j => f j.succ) h.2 i'

public theorem allFin_of : ∀ {n : Nat} (f : Fin n → Bool), (∀ i : Fin n, f i = true) →
    allFin f = true := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro f h
    rw [allFin_succ, Bool.and_eq_true]
    exact ⟨h 0, ih (fun j => f j.succ) (fun j => h j.succ)⟩

/-! ## Sums over an initial segment of `Nat` -/

@[expose] public def sumN (f : Nat → Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih => f k + ih) m

public theorem sumN_succ (f : Nat → Nat) (m : Nat) : sumN f (m + 1) = f m + sumN f m := rfl

public theorem sumN_le_of_le_one (f : Nat → Nat) (h : ∀ k, f k ≤ 1) :
    ∀ m, sumN f m ≤ m := by
  intro m
  induction m with
  | zero => exact Nat.le_refl 0
  | succ n ih => rw [sumN_succ]; have h1 := h n; omega

public theorem sumN_front (f : Nat → Nat) :
    ∀ m, f 0 + sumN (fun j => f (j + 1)) m = sumN f (m + 1) := by
  intro m
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [sumN_succ, sumN_succ (f := f), ← ih]
    omega

public theorem sumNat_eq_sumN : ∀ (m : Nat) (f : Nat → Nat),
    Vec.sumNat (n := m) (fun k => f k.val) = sumN f m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ n ih =>
    intro f
    show f 0 + Vec.sumNat (fun i : Fin n => f (Fin.succ i).val) = sumN f (n + 1)
    have h : ∀ i : Fin n, f (Fin.succ i).val = f (i.val + 1) := fun i => rfl
    rw [Vec.sumNat_congr h, ih (fun j => f (j + 1)), sumN_front]

/-! ## Base-`B` packing -/

@[expose] public def pk (B : Nat) (v : Nat → Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih => v k * B ^ k + ih) m

public theorem pk_succ (B : Nat) (v : Nat → Nat) (m : Nat) :
    pk B v (m + 1) = v m * B ^ m + pk B v m := rfl

public theorem pk_lt (B : Nat) (v : Nat → Nat) :
    ∀ m, (∀ k, k < m → v k < B) → pk B v m < B ^ m := by
  intro m
  induction m with
  | zero => intro _; show (0 : Nat) < B ^ 0; rw [Nat.pow_zero]; exact Nat.zero_lt_one
  | succ n ih =>
    intro h
    have h1 : pk B v n < B ^ n := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have h2 : v n + 1 ≤ B := h n (Nat.lt_succ_self n)
    have h3 : pk B v (n + 1) < (v n + 1) * B ^ n := by
      rw [pk_succ, Nat.succ_mul]
      exact Nat.add_lt_add_left h1 _
    have h4 : (v n + 1) * B ^ n ≤ B * B ^ n := Nat.mul_le_mul h2 (Nat.le_refl _)
    have h5 : B * B ^ n = B ^ (n + 1) := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
    exact h5 ▸ Nat.lt_of_lt_of_le h3 h4

public theorem pk_digit (B : Nat) (hB : 0 < B) (v : Nat → Nat) :
    ∀ m, (∀ k, k < m → v k < B) → ∀ j, j < m → pk B v m / B ^ j % B = v j := by
  intro m
  induction m with
  | zero => intro _ j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro h j hj
    have hb : ∀ k, k < n → v k < B := fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hpn : pk B v n < B ^ n := pk_lt B v n hb
    have hpj : 0 < B ^ j := Nat.pow_pos_iff.mpr (Or.inl hB)
    rcases Nat.lt_or_ge j n with hjn | hjn
    · have hsplit : B ^ n = B ^ (n - j - 1 + 1) * B ^ j := by
        rw [← Nat.pow_add]; congr 1; omega
      have hstep : pk B v (n + 1) / B ^ j = pk B v n / B ^ j + v n * B ^ (n - j - 1 + 1) := by
        rw [pk_succ, hsplit, ← Nat.mul_assoc, Nat.add_comm]
        exact Nat.add_mul_div_right _ _ hpj
      have hmul : v n * B ^ (n - j - 1 + 1) = (v n * B ^ (n - j - 1)) * B := by
        rw [Nat.pow_succ, ← Nat.mul_assoc]
      rw [hstep, hmul, Nat.add_mul_mod_self_right]
      exact ih hb j hjn
    · have hj' : j = n := Nat.le_antisymm (Nat.le_of_lt_succ hj) hjn
      subst hj'
      have hstep : pk B v (j + 1) / B ^ j = v j := by
        rw [pk_succ, Nat.add_comm]
        rw [Nat.add_mul_div_right _ _ hpj, Nat.div_eq_of_lt hpn, Nat.zero_add]
      rw [hstep]
      exact Nat.mod_eq_of_lt (h j (Nat.lt_succ_self j))

public theorem pk_inj (B : Nat) (hB : 0 < B) (v w : Nat → Nat) (m : Nat)
    (hv : ∀ k, k < m → v k < B) (hw : ∀ k, k < m → w k < B)
    (h : pk B v m = pk B w m) : ∀ j, j < m → v j = w j := by
  intro j hj
  rw [← pk_digit B hB v m hv j hj, ← pk_digit B hB w m hw j hj, h]

public theorem pk_zeroFun (B : Nat) : ∀ m, pk B (fun _ => 0) m = 0 := by
  intro m
  induction m with
  | zero => rfl
  | succ n ih => rw [pk_succ, ih]; simp

public theorem pk_add (B : Nat) (v w : Nat → Nat) :
    ∀ m, pk B (fun j => v j + w j) m = pk B v m + pk B w m := by
  intro m
  induction m with
  | zero => rfl
  | succ n ih => rw [pk_succ, pk_succ, pk_succ, ih, Nat.add_mul]; omega

public theorem pk_smul (B : Nat) (c : Nat) (v : Nat → Nat) :
    ∀ m, pk B (fun j => c * v j) m = c * pk B v m := by
  intro m
  induction m with
  | zero => rfl
  | succ n ih => rw [pk_succ, pk_succ, ih, Nat.mul_add, Nat.mul_assoc]

public theorem pk_sumN (B : Nat) (c : Nat → Nat) (M : Nat → Nat → Nat) (m : Nat) :
    ∀ n, sumN (fun k => c k * pk B (M k) m) n
      = pk B (fun j => sumN (fun k => c k * M k j) n) m := by
  intro n
  induction n with
  | zero => exact (pk_zeroFun B m).symm
  | succ p ih =>
    show c p * pk B (M p) m + sumN (fun k => c k * pk B (M k) m) p = _
    rw [ih, ← pk_smul, ← pk_add]
    rfl


/-! ## Coordinate bounds from the norm

A root has `sum_i y_i^2 = 8`, so every coordinate is bounded, and that bound
is what turns `D11` into a finite search. -/

public theorem sumInt_nonneg : ∀ {n : Nat} (f : Vec n Int), (∀ i, 0 ≤ f i) →
    0 ≤ Vec.sumInt f := by
  intro n
  induction n with
  | zero => intro _ _; exact Int.le_refl 0
  | succ k ih =>
    intro f h
    show 0 ≤ f 0 + Vec.sumInt (fun i => f i.succ)
    have h1 := h 0
    have h2 := ih (fun i => f i.succ) (fun i => h i.succ)
    omega

public theorem sumInt_term_le : ∀ {n : Nat} (f : Vec n Int), (∀ i, 0 ≤ f i) →
    ∀ j : Fin n, f j ≤ Vec.sumInt f := by
  intro n
  induction n with
  | zero => intro _ _ j; exact j.elim0
  | succ k ih =>
    intro f h j
    show f j ≤ f 0 + Vec.sumInt (fun i => f i.succ)
    refine Fin.cases ?_ ?_ j
    · have h2 := sumInt_nonneg (fun i : Fin k => f i.succ) (fun i => h i.succ)
      omega
    · intro j'
      have h1 := ih (fun i : Fin k => f i.succ) (fun i => h i.succ) j'
      have h2 := h 0
      omega

public theorem coord_bound {a : Int} (h : a * a ≤ 8) : -2 ≤ a ∧ a ≤ 2 := by
  refine ⟨?_, ?_⟩
  · by_cases hc : -2 ≤ a
    · exact hc
    · exfalso
      have h4 : (3 : Int) ≤ -a := by omega
      have h5 : (3 : Int) * 3 ≤ (-a) * (-a) := Int.mul_le_mul h4 h4 (by decide) (by omega)
      rw [Int.neg_mul_neg] at h5
      omega
  · by_cases hc : a ≤ 2
    · exact hc
    · exfalso
      have h3 : (3 : Int) ≤ a := by omega
      have h5 : (3 : Int) * 3 ≤ a * a := Int.mul_le_mul h3 h3 (by decide) (by omega)
      omega

public theorem sumInt_congr {n : Nat} {x y : Vec n Int} (h : ∀ i, x i = y i) :
    Vec.sumInt x = Vec.sumInt y := by
  rw [Vec.sumInt_eq_sum, Vec.sumInt_eq_sum]; exact Vec.sum_congr h

public theorem mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have h2 := Int.mul_nonneg (Int.neg_nonneg.mpr h) (Int.neg_nonneg.mpr h)
    rwa [Int.neg_mul_neg] at h2

public theorem sumInt_negate {n : Nat} (y : Vec n Int) :
    Vec.sumInt (fun i => -(y i)) = -(Vec.sumInt y) := by
  rw [Vec.sumInt_eq_sum, Vec.sumInt_eq_sum]
  exact Vec.sum_neg y

public theorem sumInt8_sub_one (y : Vec 8 Int) :
    Vec.sumInt (fun i => y i - 1) = Vec.sumInt y - 8 := by
  rw [Vec.sumInt_eq_sum, Vec.sumInt_eq_sum]
  have h1 : Vec.sum (fun i : Fin 8 => y i - 1)
      = Vec.sum (fun i : Fin 8 => add (y i) (-1 : Int)) := rfl
  have h2 : nsmul 8 (-1 : Int) = -8 := by decide
  rw [h1, Vec.sum_add y (fun _ => (-1 : Int)), Vec.sum_const (-1 : Int), h2]
  show Vec.sum y + (-8 : Int) = Vec.sum y - 8
  omega

/-! ## Flat `8`-term sums

`Vec.sumInt` is a structural recursion, and the kernel re-runs its unfolding
-- closure per level -- at every one of the `120^2` inner products and every
one of the `6561 + 256` search candidates. Writing the eight terms out flat
gives the same value definitionally, `sum8_eq` and `dot8_eq` being `rfl`, at a
fraction of the reduction and of the memory the kernel holds while doing it. -/

@[expose] public def sum8 (x : Vec 8 Int) : Int :=
  x 0 + (x 1 + (x 2 + (x 3 + (x 4 + (x 5 + (x 6 + (x 7 + 0)))))))

public theorem sum8_eq (x : Vec 8 Int) : sum8 x = Vec.sumInt x := rfl

@[expose] public def dot8 (x y : Vec 8 Int) : Int :=
  x 0 * y 0 + (x 1 * y 1 + (x 2 * y 2 + (x 3 * y 3 + (x 4 * y 4 + (x 5 * y 5
    + (x 6 * y 6 + (x 7 * y 7 + 0)))))))

public theorem dot8_eq (x y : Vec 8 Int) : dot8 x y = dot x y := rfl

/-! ## `D9`-`D11`: the ambient lattice and its roots -/

/-- `D9`. `D := { x in Z^O : sum_i x_i = 0 (mod 2) }`, read in the 2x scaling:
`x` has all coordinates in `Z` iff `y = 2x` has all coordinates even, and
`sum_i x_i = 0 (mod 2)` iff `sum_i y_i = 0 (mod 4)`. -/
@[expose] public def D9 (y : Vec 8 Int) : Prop :=
  (∀ i, y i % 2 = 0) ∧ Vec.sumInt y % 4 = 0

/-- `D10`. `L := D union (D + (1/2, ..., 1/2))`; in the 2x scaling the glue
vector is `(1, ..., 1)`, so the second sheet is `{ y : y - (1,...,1) in D }`. -/
@[expose] public def D10 (y : Vec 8 Int) : Prop := D9 y ∨ D9 (fun i => y i - 1)

/-- `D11`. `R := { x in L : <x,x> = 2 }`; in the 2x scaling `<y,y> = 8`. -/
@[expose] public def D11 (y : Vec 8 Int) : Prop := D10 y ∧ dot y y = 8

/-! ### The `n = 8` lattice is the general glue lattice

`Glue.lean` builds `L_n` for every `n` and proves `T57a`-`T57c`, `T84` and
`T85` about it; this module builds the lattice at `n = 8` in the decidable
shape the root enumeration needs. The document has one `L`, not two, so the
two presentations are proved equal here. Without this bridge the counting
theorems and the dimension-specificity theorems would be about formally
unrelated objects, and nothing in the build would say so. -/

public theorem D9_iff_MemD (y : Vec 8 Int) : D9 y ↔ Glue.MemD 8 y :=
  (Glue.MemD_iff 8 y).symm

public theorem sumInt_sub_one (y : Vec 8 Int) :
    Vec.sumInt (fun i => y i - 1) = Vec.sumInt y - 8 := by
  have h : (fun i : Fin 8 => y i - 1) = fun i : Fin 8 => y i + (-1) := by
    funext i; omega
  rw [h, Glue.sumInt_add, Glue.sumInt_const]
  omega

public theorem D10_iff_MemL (y : Vec 8 Int) : D10 y ↔ Glue.MemL 8 y := by
  constructor
  · rintro (h | h)
    · exact Or.inl ((D9_iff_MemD y).mp h)
    · refine Or.inr ((Glue.MemGlue_iff 8 y).mpr ⟨fun i => ?_, ?_⟩)
      · have hi : (y i - 1) % 2 = 0 := h.1 i
        omega
      · have hs : Vec.sumInt (fun i => y i - 1) % 4 = 0 := h.2
        rw [sumInt_sub_one] at hs
        omega
  · rintro (h | h)
    · exact Or.inl ((D9_iff_MemD y).mpr h)
    · have hc := (Glue.MemGlue_iff 8 y).mp h
      refine Or.inr ⟨fun i => ?_, ?_⟩
      · have hi : y i % 2 = 1 := hc.1 i
        show (y i - 1) % 2 = 0
        omega
      · show Vec.sumInt (fun i => y i - 1) % 4 = 0
        rw [sumInt_sub_one]
        have hs := hc.2
        omega

/-- `D11`'s roots are exactly the norm-`8` vectors of the general glue lattice
at `n = 8`, so `T5` counts roots of the same `L` that `T57c` characterises. -/
public theorem D11_iff (y : Vec 8 Int) : D11 y ↔ (Glue.MemL 8 y ∧ dot y y = Glue.rootNorm) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(D10_iff_MemL y).mp h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(D10_iff_MemL y).mpr h1, h2⟩

@[expose] public def isD9 (y : Vec 8 Int) : Bool :=
  allFin (fun i => decide (y i % 2 = 0)) && decide (sum8 y % 4 = 0)

@[expose] public def isD10 (y : Vec 8 Int) : Bool := isD9 y || isD9 (fun i => y i - 1)

/-- The norm test comes first because `Bool.and` is lazy on `false`: in the
`3^8` search below it rejects all but `112` of the `6561` candidates before any
parity test runs. -/
@[expose] public def isD11 (y : Vec 8 Int) : Bool := decide (dot8 y y = 8) && isD10 y

public theorem isD9_iff (y : Vec 8 Int) : isD9 y = true ↔ D9 y := by
  constructor
  · intro h
    rw [isD9, Bool.and_eq_true] at h
    refine ⟨fun i => of_decide_eq_true (allFin_true _ h.1 i), ?_⟩
    have h2 := of_decide_eq_true h.2
    rwa [sum8_eq] at h2
  · intro h
    rw [isD9, Bool.and_eq_true]
    refine ⟨allFin_of _ (fun i => decide_eq_true (h.1 i)), decide_eq_true ?_⟩
    rw [sum8_eq]
    exact h.2

public theorem isD10_iff (y : Vec 8 Int) : isD10 y = true ↔ D10 y := by
  rw [isD10, Bool.or_eq_true, isD9_iff, isD9_iff]; rfl

public theorem isD11_iff (y : Vec 8 Int) : isD11 y = true ↔ D11 y := by
  rw [isD11, Bool.and_eq_true, isD10_iff]
  exact ⟨fun h => ⟨h.2, of_decide_eq_true h.1⟩, fun h => ⟨decide_eq_true h.2, h.1⟩⟩

public theorem D11_neg {y : Vec 8 Int} (h : D11 y) : D11 (neg y) := by
  have hn : ∀ i : Fin 8, (neg y : Vec 8 Int) i = -(y i) := fun _ => rfl
  have hsum : Vec.sumInt (neg y : Vec 8 Int) = -(Vec.sumInt y) := sumInt_negate y
  refine ⟨?_, ?_⟩
  · rcases h.1 with he | ho
    · refine Or.inl ⟨fun i => ?_, ?_⟩
      · have h1 : y i % 2 = 0 := he.1 i
        have h2 := hn i
        omega
      · have h2 : Vec.sumInt y % 4 = 0 := he.2
        show Vec.sumInt (neg y : Vec 8 Int) % 4 = 0
        omega
    · refine Or.inr ⟨fun i => ?_, ?_⟩
      · have h1 : (y i - 1) % 2 = 0 := ho.1 i
        have h2 := hn i
        show ((neg y : Vec 8 Int) i - 1) % 2 = 0
        omega
      · have h2 : Vec.sumInt (fun i => y i - 1) % 4 = 0 := ho.2
        rw [sumInt8_sub_one] at h2
        have h3 : Vec.sumInt (fun i => (neg y : Vec 8 Int) i - 1)
            = Vec.sumInt (neg y : Vec 8 Int) - 8 := sumInt8_sub_one _
        show Vec.sumInt (fun i => (neg y : Vec 8 Int) i - 1) % 4 = 0
        omega
  · have h1 : dot y y = 8 := h.2
    show dot (neg y) (neg y) = 8
    rw [dot_neg_left, dot_neg_right]
    omega

/-! ## The `120` class representatives

One `32`-bit word per class, four bits per coordinate holding `y_j + 2`, which
is in `[0,4]` for every root. The words are listed least significant first;
class `i` occupies bits `[32i, 32i+32)`. Nothing about this table is asserted:
`repIsRoot` proves every entry is a root, `T5` and `T6` prove the list is
exactly `R` up to sign, and `master` proves the enumeration is complete. -/
@[expose] public def repWords : List Nat :=
  [
    0x22222244, 0x22222204, 0x22222424, 0x22222024, 0x22224224,
    0x22220224, 0x22242224, 0x22202224, 0x22422224, 0x22022224,
    0x24222224, 0x20222224, 0x42222224, 0x02222224, 0x22222442,
    0x22222042, 0x22224242, 0x22220242, 0x22242242, 0x22202242,
    0x22422242, 0x22022242, 0x24222242, 0x20222242, 0x42222242,
    0x02222242, 0x22224422, 0x22220422, 0x22242422, 0x22202422,
    0x22422422, 0x22022422, 0x24222422, 0x20222422, 0x42222422,
    0x02222422, 0x22244222, 0x22204222, 0x22424222, 0x22024222,
    0x24224222, 0x20224222, 0x42224222, 0x02224222, 0x22442222,
    0x22042222, 0x24242222, 0x20242222, 0x42242222, 0x02242222,
    0x24422222, 0x20422222, 0x42422222, 0x02422222, 0x44222222,
    0x04222222, 0x33333333, 0x11333333, 0x13133333, 0x31133333,
    0x13313333, 0x31313333, 0x33113333, 0x11113333, 0x13331333,
    0x31331333, 0x33131333, 0x11131333, 0x33311333, 0x11311333,
    0x13111333, 0x31111333, 0x13333133, 0x31333133, 0x33133133,
    0x11133133, 0x33313133, 0x11313133, 0x13113133, 0x31113133,
    0x33331133, 0x11331133, 0x13131133, 0x31131133, 0x13311133,
    0x31311133, 0x33111133, 0x11111133, 0x13333313, 0x31333313,
    0x33133313, 0x11133313, 0x33313313, 0x11313313, 0x13113313,
    0x31113313, 0x33331313, 0x11331313, 0x13131313, 0x31131313,
    0x13311313, 0x31311313, 0x33111313, 0x11111313, 0x33333113,
    0x11333113, 0x13133113, 0x31133113, 0x13313113, 0x31313113,
    0x33113113, 0x11113113, 0x13331113, 0x31331113, 0x33131113,
    0x11131113, 0x33311113, 0x11311113, 0x13111113, 0x31111113
  ]

@[expose] public def repTable : Nat := repWords.foldr (fun v acc => acc * 4294967296 + v) 0

@[expose] public def wordAt (i : Nat) : Nat := (repTable >>> (32 * i)) &&& 4294967295

@[expose] public def repN (i : Nat) : Vec 8 Int :=
  fun j => (((wordAt i >>> (4 * j.val)) &&& 15 : Nat) : Int) - 2

/-- The nibble of a coordinate: the inverse of the table's `y_j + 2` encoding. -/
@[expose] public def nib (a : Int) : Nat := (a + 2).toNat

/-- A vector's table word. Comparing words is `120` machine comparisons where
comparing vectors would be `120 * 8` kernel reductions. -/
@[expose] public def codeOf (y : Vec 8 Int) : Nat :=
  nib (y 0) + 16 * (nib (y 1) + 16 * (nib (y 2) + 16 * (nib (y 3) + 16 * (nib (y 4)
    + 16 * (nib (y 5) + 16 * (nib (y 6) + 16 * nib (y 7)))))))

/-- Linear search for a class by its word, returning `120` when there is none. -/
@[expose] public def findCode (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 120 (fun k ih => if wordAt k = c then k else ih) 120

/-- A linear functional that separates `x` from `-x` on `R`. Base-`3` weights
work because a root is either `(+-2, +-2, 0^6)`, where the two powers of `3`
differ, or `(+-1)^8`, where a base-`3` digit sum of `+-1`s is never zero. This
replaces a "first nonzero coordinate" convention by one `dot`, and
`dot_neg_left` then gives the sign flip for free. -/
@[expose] public def posRef : Vec 8 Int := fun j => ((3 ^ (7 - j.val) : Nat) : Int)

/-- The representative of the class of `x`: the one of `x`, `-x` on which
`posRef` is positive. -/
@[expose] public def nrm (x : Vec 8 Int) : Vec 8 Int := if 0 < dot x posRef then x else neg x

public theorem nrm_eq (x : Vec 8 Int) :
    nrm x = if 0 < dot x posRef then x else neg x := rfl

/-- The predicate the `3^8` and `2^8` searches below decide: every root is the
signed image of the table entry its word selects. -/
@[expose] public def chk (y : Vec 8 Int) : Bool :=
  !isD11 y || (decide (findCode (codeOf (nrm y)) < 120)
    && allFin (fun j => decide (nrm y j = repN (findCode (codeOf (nrm y))) j)))

/-- Base-`3` decoding of the all-even branch: `n` ranges over `[0, 3^8)` and
`decEven n` over `{-2,0,2}^8`. -/
@[expose] public def decEven (n : Nat) : Vec 8 Int :=
  fun j => 2 * (((n / 3 ^ j.val) % 3 : Nat) : Int) - 2

/-- Base-`2` decoding of the all-odd branch: `n` ranges over `[0, 2^8)` and
`decOdd n` over `{-1,1}^8`. -/
@[expose] public def decOdd (n : Nat) : Vec 8 Int :=
  fun j => 1 - 2 * (((n / 2 ^ j.val) % 2 : Nat) : Int)

@[expose] public def idx8 (k : Nat) : Fin 8 := ⟨k % 8, Nat.mod_lt _ (by decide)⟩

public theorem idx8_val (i : Fin 8) : idx8 i.val = i :=
  Fin.eq_of_val_eq (Nat.mod_eq_of_lt i.isLt)

public theorem exists_decEven (y : Vec 8 Int) (h : ∀ i : Fin 8, y i = -2 ∨ y i = 0 ∨ y i = 2) :
    ∃ n, n < 6561 ∧ ∀ j : Fin 8, decEven n j = y j := by
  have hb : ∀ k, k < 8 → ((y (idx8 k) + 2) / 2).toNat < 3 := by
    intro k _
    rcases h (idx8 k) with hh | hh | hh <;> rw [hh] <;> decide
  refine ⟨pk 3 (fun k => ((y (idx8 k) + 2) / 2).toNat) 8, ?_, ?_⟩
  · have hlt := pk_lt 3 (fun k => ((y (idx8 k) + 2) / 2).toNat) 8 hb
    exact hlt
  · intro j
    have hd := pk_digit 3 (by decide) (fun k => ((y (idx8 k) + 2) / 2).toNat) 8 hb j.val j.isLt
    show 2 * ((pk 3 (fun k => ((y (idx8 k) + 2) / 2).toNat) 8 / 3 ^ j.val % 3 : Nat) : Int) - 2
      = y j
    rw [hd, idx8_val]
    rcases h j with hh | hh | hh <;> rw [hh] <;> decide

public theorem exists_decOdd (y : Vec 8 Int) (h : ∀ i : Fin 8, y i = -1 ∨ y i = 1) :
    ∃ n, n < 256 ∧ ∀ j : Fin 8, decOdd n j = y j := by
  have hb : ∀ k, k < 8 → (if y (idx8 k) = 1 then 0 else 1) < 2 := by
    intro k _
    rcases h (idx8 k) with hh | hh <;> rw [hh] <;> decide
  refine ⟨pk 2 (fun k => if y (idx8 k) = 1 then 0 else 1) 8, ?_, ?_⟩
  · exact pk_lt 2 (fun k => if y (idx8 k) = 1 then 0 else 1) 8 hb
  · intro j
    have hd := pk_digit 2 (by decide) (fun k => if y (idx8 k) = 1 then 0 else 1) 8 hb j.val j.isLt
    show 1 - 2 * ((pk 2 (fun k => if y (idx8 k) = 1 then 0 else 1) 8 / 2 ^ j.val % 2 : Nat) : Int)
      = y j
    rw [hd, idx8_val]
    rcases h j with hh | hh <;> rw [hh] <;> decide

/-! ## The enumeration of `R`, proved complete

`boxEven` and `boxOdd` are the two finite searches. Together with the
coordinate bound they say that every root is the signed image of exactly one
table entry, which is `master`. -/

/-- The all-even branch of the search, cut into nine blocks of `729`.

The kernel holds every intermediate value of a `decide` until the declaration
it belongs to is finished, and releases them afterwards. Measured on this
module: the search as one block of `6561` peaks at `1.8 GB` of resident
memory, the same search as nine blocks at `0.8 GB`, for the same total work.
The split is a memory bound, not a speed one. -/
@[expose] public def chkEven (b n : Nat) : Bool := chk (decEven (b + n))

public theorem boxEven0 : allLt (chkEven 0) 729 = true := by decide +kernel

public theorem boxEven1 : allLt (chkEven 729) 729 = true := by decide +kernel

public theorem boxEven2 : allLt (chkEven 1458) 729 = true := by decide +kernel

public theorem boxEven3 : allLt (chkEven 2187) 729 = true := by decide +kernel

public theorem boxEven4 : allLt (chkEven 2916) 729 = true := by decide +kernel

public theorem boxEven5 : allLt (chkEven 3645) 729 = true := by decide +kernel

public theorem boxEven6 : allLt (chkEven 4374) 729 = true := by decide +kernel

public theorem boxEven7 : allLt (chkEven 5103) 729 = true := by decide +kernel

public theorem boxEven8 : allLt (chkEven 5832) 729 = true := by decide +kernel

public theorem boxOdd : allLt (fun n => chk (decOdd n)) 256 = true := by decide +kernel

public theorem boxEven_all (n : Nat) (h : n < 6561) : chk (decEven n) = true := by
  have step : ∀ b : Nat, allLt (chkEven b) 729 = true → b ≤ n → n < b + 729 →
      chk (decEven n) = true := by
    intro b hb h1 h2
    have h3 : chk (decEven (b + (n - b))) = true := allLt_true _ _ hb (n - b) (by omega)
    rwa [show b + (n - b) = n from by omega] at h3
  rcases Nat.lt_or_ge n 729 with h0 | h0
  · exact step 0 boxEven0 (Nat.zero_le n) (by omega)
  rcases Nat.lt_or_ge n 1458 with h1 | h1
  · exact step 729 boxEven1 h0 (by omega)
  rcases Nat.lt_or_ge n 2187 with h2 | h2
  · exact step 1458 boxEven2 h1 (by omega)
  rcases Nat.lt_or_ge n 2916 with h3 | h3
  · exact step 2187 boxEven3 h2 (by omega)
  rcases Nat.lt_or_ge n 3645 with h4 | h4
  · exact step 2916 boxEven4 h3 (by omega)
  rcases Nat.lt_or_ge n 4374 with h5 | h5
  · exact step 3645 boxEven5 h4 (by omega)
  rcases Nat.lt_or_ge n 5103 with h6 | h6
  · exact step 4374 boxEven6 h5 (by omega)
  rcases Nat.lt_or_ge n 5832 with h7 | h7
  · exact step 5103 boxEven7 h6 (by omega)
  exact step 5832 boxEven8 h7 (by omega)

public theorem chk_of_root (y : Vec 8 Int) (h : D11 y) : chk y = true := by
  have hsq : ∀ i : Fin 8, y i * y i ≤ 8 := by
    intro i
    have h0 : ∀ i : Fin 8, 0 ≤ y i * y i := fun i => mul_self_nonneg (y i)
    have := sumInt_term_le (fun i => y i * y i) h0 i
    have h2 : Vec.sumInt (fun i => y i * y i) = 8 := h.2
    omega
  have hbd : ∀ i : Fin 8, -2 ≤ y i ∧ y i ≤ 2 := fun i => coord_bound (hsq i)
  rcases h.1 with he | ho
  · have hval : ∀ i : Fin 8, y i = -2 ∨ y i = 0 ∨ y i = 2 := by
      intro i
      have h1 := he.1 i
      have h2 := hbd i
      omega
    obtain ⟨n, hn, hy⟩ := exists_decEven y hval
    have hc := boxEven_all n hn
    rwa [funext hy] at hc
  · have hval : ∀ i : Fin 8, y i = -1 ∨ y i = 1 := by
      intro i
      have h1 : (y i - 1) % 2 = 0 := ho.1 i
      have h2 := hbd i
      omega
    obtain ⟨n, hn, hy⟩ := exists_decOdd y hval
    have hc := allLt_true _ _ boxOdd n hn
    rwa [funext hy] at hc

public theorem master (y : Vec 8 Int) (h : D11 y) :
    findCode (codeOf (nrm y)) < 120
      ∧ ∀ j : Fin 8, nrm y j = repN (findCode (codeOf (nrm y))) j := by
  have hc := chk_of_root y h
  rw [chk, Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · rw [(isD11_iff y).mpr h] at hc
    exact absurd hc (by decide)
  · rw [Bool.and_eq_true] at hc
    exact ⟨of_decide_eq_true hc.1, fun j => of_decide_eq_true (allFin_true _ hc.2 j)⟩

/-! ## `D12`, `T5`, `T6` -/

/-- The carrier of `D12`'s quotient. `K := R / {+1,-1}` is presented by the
`120` representatives of `repWords`, so `K` is `Fin 120`. -/
public abbrev K : Type := Fin 120

/-- The chosen representative of a class. -/
@[expose] public def rep (i : K) : Vec 8 Int := repN i.val

/-- `D12`. `K := R / {+1,-1}`, with `k(x)` the class of `x`. This is `k`:
a root is sent to the index of the representative of its sign pair.
`D12_eq_iff` is the defining property of the quotient, and `T6` is that the
`120` representatives meet every class exactly once. -/
@[expose] public def D12 (x : Vec 8 Int) : K :=
  ⟨findCode (codeOf (nrm x)) % 120, Nat.mod_lt _ (by decide)⟩

public theorem repIsRoot : allLt (fun i => isD11 (repN i)) 120 = true := by decide +kernel

public theorem repPos : allLt (fun i => decide (0 < dot (repN i) posRef)) 120 = true := by
  decide +kernel

public theorem repFind : allLt (fun i => decide (findCode (codeOf (repN i)) = i)) 120 = true := by
  decide +kernel

public theorem D11_rep (i : K) : D11 (rep i) :=
  (isD11_iff _).mp (allLt_true _ _ repIsRoot i.val i.isLt)

public theorem dot_rep_pos (i : K) : 0 < dot (rep i) posRef :=
  of_decide_eq_true (allLt_true _ _ repPos i.val i.isLt)

public theorem nrm_rep (i : K) : nrm (rep i) = rep i := if_pos (dot_rep_pos i)

public theorem D12_rep (i : K) : D12 (rep i) = i := by
  have h2 : findCode (codeOf (rep i)) = i.val :=
    of_decide_eq_true (allLt_true _ _ repFind i.val i.isLt)
  refine Fin.eq_of_val_eq ?_
  show findCode (codeOf (nrm (rep i))) % 120 = i.val
  rw [nrm_rep, h2, Nat.mod_eq_of_lt i.isLt]

public theorem rep_D12 {x : Vec 8 Int} (h : D11 x) : rep (D12 x) = nrm x := by
  obtain ⟨hlt, heq⟩ := master x h
  show repN (findCode (codeOf (nrm x)) % 120) = nrm x
  rw [Nat.mod_eq_of_lt hlt]
  exact (funext heq).symm

public theorem vneg_neg (x : Vec 8 Int) : neg (neg x) = x :=
  funext (fun i => Int.neg_neg (x i))

public theorem D12_of_nrm {z w : Vec 8 Int} (h : nrm z = nrm w) : D12 z = D12 w :=
  Fin.eq_of_val_eq (by
    show findCode (codeOf (nrm z)) % 120 = findCode (codeOf (nrm w)) % 120
    rw [h])

public theorem dot_sign {x : Vec 8 Int} (h : D11 x) :
    0 < dot x posRef ∨ dot x posRef < 0 := by
  by_cases hp : 0 < dot x posRef
  · exact Or.inl hp
  · refine Or.inr ?_
    have h2 : 0 < dot (nrm x) posRef := by rw [← rep_D12 h]; exact dot_rep_pos _
    rw [nrm_eq, if_neg hp, dot_neg_left] at h2
    omega

/-- `T6`. `|K| = 120`: `rep` is a section of the class map hitting every class
exactly once, so the classes are in bijection with `Fin 120`. -/
public theorem T6 :
    (∀ i : K, D11 (rep i) ∧ D12 (rep i) = i)
      ∧ (∀ x, D11 x → rep (D12 x) = x ∨ rep (D12 x) = neg x) := by
  refine ⟨fun i => ⟨D11_rep i, D12_rep i⟩, fun x h => ?_⟩
  rw [rep_D12 h, nrm_eq]
  by_cases hp : 0 < dot x posRef
  · exact Or.inl (if_pos hp)
  · exact Or.inr (if_neg hp)

/-- `D12`'s quotient property: two roots have the same class exactly when they
agree up to the sign action of `{+1,-1}`. -/
public theorem nrm_neg {z : Vec 8 Int} (hz : D11 z) : nrm (neg z) = nrm z := by
  have hd : dot (neg z) posRef = -(dot z posRef) := dot_neg_left z posRef
  rcases dot_sign hz with hs | hs
  · simp only [nrm_eq]
    rw [if_pos hs, if_neg (by omega : ¬ 0 < dot (neg z) posRef), vneg_neg]
  · simp only [nrm_eq]
    rw [if_neg (by omega : ¬ 0 < dot z posRef), if_pos (by omega : 0 < dot (neg z) posRef)]

/-- `D12`'s quotient property: two roots have the same class exactly when they
agree up to the sign action of `{+1,-1}`. -/
public theorem D12_eq_iff {x y : Vec 8 Int} (hx : D11 x) (hy : D11 y) :
    D12 x = D12 y ↔ (y = x ∨ y = neg x) := by
  constructor
  · intro h
    have hxx : nrm x = nrm y := by rw [← rep_D12 hx, ← rep_D12 hy, h]
    simp only [nrm_eq] at hxx
    by_cases hpx : 0 < dot x posRef <;> by_cases hpy : 0 < dot y posRef
    · rw [if_pos hpx, if_pos hpy] at hxx
      exact Or.inl hxx.symm
    · rw [if_pos hpx, if_neg hpy] at hxx
      refine Or.inr ?_
      rw [hxx, vneg_neg]
    · rw [if_neg hpx, if_pos hpy] at hxx
      exact Or.inr hxx.symm
    · rw [if_neg hpx, if_neg hpy] at hxx
      refine Or.inl ?_
      have h2 := congrArg neg hxx
      rw [vneg_neg, vneg_neg] at h2
      exact h2.symm
  · intro hcase
    rcases hcase with hc | hc
    · rw [hc]
    · exact D12_of_nrm (by rw [hc]; exact (nrm_neg hx).symm)

/-- The `240` roots, indexed: the first `120` are the class representatives and
the last `120` their negatives. -/
@[expose] public def R240 (i : Fin 240) : Vec 8 Int :=
  if i.val < 120 then repN i.val else neg (repN (i.val - 120))

/-- `T5`. `|R| = 240`: `R240` is a bijection from `Fin 240` onto `R`. -/
public theorem T5 :
    (∀ i : Fin 240, D11 (R240 i))
      ∧ (∀ i j : Fin 240, R240 i = R240 j → i = j)
      ∧ (∀ x, D11 x → ∃ i : Fin 240, x = R240 i) := by
  have hrep : ∀ (m : Nat) (hm : m < 120), repN m = rep ⟨m, hm⟩ := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < 120
    · rw [R240, if_pos hi, hrep i.val hi]; exact D11_rep _
    · rw [R240, if_neg hi]
      exact D11_neg (D11_rep ⟨i.val - 120, by omega⟩)
  · intro i j hij
    have key : ∀ (a b : Nat) (ha : a < 120) (hb : b < 120), repN a = repN b → a = b := by
      intro a b ha hb h
      have heq : rep ⟨a, ha⟩ = rep ⟨b, hb⟩ := h
      have h1 : D12 (rep ⟨a, ha⟩) = D12 (rep ⟨b, hb⟩) := by rw [heq]
      rw [D12_rep, D12_rep] at h1
      exact congrArg Fin.val h1
    have hne : ∀ (a b : Nat) (ha : a < 120) (hb : b < 120), repN a ≠ neg (repN b) := by
      intro a b ha hb h
      have h1 : 0 < dot (repN a) posRef := dot_rep_pos ⟨a, ha⟩
      have h2 : 0 < dot (repN b) posRef := dot_rep_pos ⟨b, hb⟩
      rw [h, dot_neg_left] at h1
      omega
    refine Fin.eq_of_val_eq ?_
    by_cases hi : i.val < 120 <;> by_cases hj : j.val < 120
    · rw [R240, R240, if_pos hi, if_pos hj] at hij
      exact key i.val j.val hi hj hij
    · rw [R240, R240, if_pos hi, if_neg hj] at hij
      exact absurd hij (hne i.val (j.val - 120) hi (by omega))
    · rw [R240, R240, if_neg hi, if_pos hj] at hij
      exact absurd hij.symm (hne j.val (i.val - 120) hj (by omega))
    · rw [R240, R240, if_neg hi, if_neg hj] at hij
      have h1 : repN (i.val - 120) = repN (j.val - 120) := by
        have := congrArg neg hij
        rwa [vneg_neg, vneg_neg] at this
      have := key (i.val - 120) (j.val - 120) (by omega) (by omega) h1
      have hi' := i.isLt
      have hj' := j.isLt
      omega
  · intro x h
    rcases dot_sign h with hs | hs
    · refine ⟨⟨(D12 x).val, by have := (D12 x).isLt; omega⟩, ?_⟩
      have h1 : rep (D12 x) = x := by rw [rep_D12 h, nrm, if_pos hs]
      rw [R240, if_pos (show (D12 x).val < 120 from (D12 x).isLt)]
      exact h1.symm
    · refine ⟨⟨(D12 x).val + 120, by have := (D12 x).isLt; omega⟩, ?_⟩
      have h1 : rep (D12 x) = neg x := by
        rw [rep_D12 h, nrm, if_neg (by omega : ¬ 0 < dot x posRef)]
      rw [R240, if_neg (by simp)]
      show x = neg (repN ((D12 x).val + 120 - 120))
      rw [show (D12 x).val + 120 - 120 = (D12 x).val from by omega]
      have : neg (rep (D12 x)) = neg (neg x) := congrArg neg h1
      rw [vneg_neg] at this
      exact this.symm

/-! ## `D13`: the class graph, and `T7`, `T8` -/

/-- Adjacency of two distinct classes. `|<u,v>| = 1` of `D13` is `|<u,v>| = 4`
in the 2x scaling. -/
@[expose] public def adjRaw (i j : Nat) : Nat :=
  if dot8 (repN i) (repN j) = 4 then 1
  else if dot8 (repN i) (repN j) = -4 then 1 else 0

/-- Adjacency on raw indices, evaluated at the canonical order of the pair.
This is the hot path of the whole module: `T7` and `T8` between them ask for
all `120^2` of these, and routing every pair through `min, max` means the
kernel evaluates the `7140` distinct inner products once rather than twice. -/
@[expose] public def adjN (i j : Nat) : Nat :=
  if i = j then 0 else if i < j then adjRaw i j else adjRaw j i

public theorem adjRaw_comm (i j : Nat) : adjRaw i j = adjRaw j i := by
  show (if dot8 (repN i) (repN j) = 4 then 1
    else if dot8 (repN i) (repN j) = -4 then 1 else 0)
      = (if dot8 (repN j) (repN i) = 4 then 1
    else if dot8 (repN j) (repN i) = -4 then 1 else 0)
  rw [dot8_eq, dot8_eq, dot_comm (repN i) (repN j)]

/-- `D13`. `G := (K,E)` where `{u,v} in E iff u != v and |<u,v>| = 1`. -/
@[expose] public def D13 (u v : K) : Prop :=
  u ≠ v ∧ (dot (rep u) (rep v) = 4 ∨ dot (rep u) (rep v) = -4)

/-- The adjacency matrix of `G`, as `0`/`1`. -/
@[expose] public def A (u v : K) : Nat := adjN u.val v.val

/-- `D14` at `W = K`: the degree of a class in `G`. -/
@[expose] public def deg (u : K) : Nat := Vec.sumNat (fun v : K => A u v)

/-- The number of common neighbours of two classes: the `(u,v)` entry of `A^2`. -/
@[expose] public def common (u v : K) : Nat := Vec.sumNat (fun k : K => A u k * A k v)

public theorem A_apply (u v : K) (h : u ≠ v) : A u v =
    (if dot (rep u) (rep v) = 4 then 1
      else if dot (rep u) (rep v) = -4 then 1 else 0) := by
  have hne : ¬ (u.val = v.val) := fun hh => h (Fin.eq_of_val_eq hh)
  show (if u.val = v.val then 0
    else if u.val < v.val then adjRaw u.val v.val else adjRaw v.val u.val) = _
  rw [if_neg hne]
  by_cases hlt : u.val < v.val
  · rw [if_pos hlt]; rfl
  · rw [if_neg hlt, adjRaw_comm]; rfl

public theorem adjRaw_le_one (i j : Nat) : adjRaw i j ≤ 1 := by
  show (if dot8 (repN i) (repN j) = 4 then 1
    else if dot8 (repN i) (repN j) = -4 then 1 else 0) ≤ 1
  split
  · decide
  · split <;> decide

public theorem adjN_le_one (i j : Nat) : adjN i j ≤ 1 := by
  show (if i = j then 0 else if i < j then adjRaw i j else adjRaw j i) ≤ 1
  split
  · decide
  · split
    · exact adjRaw_le_one _ _
    · exact adjRaw_le_one _ _

public theorem adjN_diag (i : Nat) : adjN i i = 0 := by
  show (if i = i then 0 else if i < i then adjRaw i i else adjRaw i i) = 0
  rw [if_pos rfl]

public theorem A_diag (u : K) : A u u = 0 := adjN_diag u.val

public theorem A_spec (u v : K) : (A u v = 1 ∧ D13 u v) ∨ (A u v = 0 ∧ ¬ D13 u v) := by
  by_cases huv : u = v
  · refine Or.inr ⟨?_, fun hd => hd.1 huv⟩
    show adjN u.val v.val = 0
    rw [congrArg Fin.val huv]
    exact adjN_diag v.val
  · by_cases h4 : dot (rep u) (rep v) = 4
    · exact Or.inl ⟨by rw [A_apply u v huv, if_pos h4], ⟨huv, Or.inl h4⟩⟩
    · by_cases h4' : dot (rep u) (rep v) = -4
      · exact Or.inl ⟨by rw [A_apply u v huv, if_neg h4, if_pos h4'], ⟨huv, Or.inr h4'⟩⟩
      · refine Or.inr ⟨by rw [A_apply u v huv, if_neg h4, if_neg h4'], fun hd => ?_⟩
        rcases hd.2 with hh | hh
        · exact h4 hh
        · exact h4' hh

public theorem A_of_D13 {u v : K} (h : D13 u v) : A u v = 1 := by
  rcases A_spec u v with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact h1
  · exact absurd h h2

public theorem A_of_not_D13 {u v : K} (h : ¬ D13 u v) : A u v = 0 := by
  rcases A_spec u v with ⟨_, h1⟩ | ⟨h2, _⟩
  · exact absurd h1 h
  · exact h2

/-! ### The packed evaluation of `A` and `A^2`

`rowPk i` is row `i` of `A` packed base `2^16`; `sqPk i` is row `i` of `A^2`
obtained as `120` additions of packed rows rather than `120^2` scalar
multiply-adds; `tgtPk i` is the strongly regular target `24J + 4A + 32I`.
`pk_inj` turns the single packed equation back into the `120` entrywise ones,
because every entry involved is below `2^16`. -/

@[expose] public def packBase : Nat := 65536

@[expose] public def rowPk (i : Nat) : Nat := pk packBase (adjN i) 120

@[expose] public def sqPk (i : Nat) : Nat := sumN (fun k => adjN i k * rowPk k) 120

@[expose] public def tgtPk (i : Nat) : Nat :=
  pk packBase (fun j => 24 + 4 * adjN i j + (if i = j then 32 else 0)) 120

@[expose] public def commonN (i j : Nat) : Nat := sumN (fun k => adjN i k * adjN k j) 120

/-- The one kernel computation behind `T7` and `T8`. Degree and packed square
are checked in a single pass so that the `120^2` inner products are evaluated
once rather than once per theorem. -/
public theorem graphComp :
    allLt (fun i => decide (sumN (adjN i) 120 = 56) && decide (sqPk i = tgtPk i)) 120 = true := by
  decide +kernel

public theorem graphFacts (i : Nat) (hi : i < 120) :
    sumN (adjN i) 120 = 56 ∧ sqPk i = tgtPk i := by
  have h := allLt_true _ _ graphComp i hi
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

public theorem commonN_lt (i j : Nat) : commonN i j < packBase := by
  have h := sumN_le_of_le_one (fun k => adjN i k * adjN k j)
    (fun k => Nat.le_trans (Nat.mul_le_mul (adjN_le_one i k) (adjN_le_one k j))
      (Nat.le_refl 1)) 120
  show sumN (fun k => adjN i k * adjN k j) 120 < 65536
  omega

public theorem tgt_lt (i j : Nat) : 24 + 4 * adjN i j + (if i = j then 32 else 0) < packBase := by
  have h := adjN_le_one i j
  show 24 + 4 * adjN i j + (if i = j then 32 else 0) < 65536
  split <;> omega

public theorem sqPk_eq (i : Nat) : sqPk i = pk packBase (fun j => commonN i j) 120 :=
  pk_sumN packBase (adjN i) adjN 120 120

public theorem commonN_eq (i j : Nat) (hi : i < 120) (hj : j < 120) :
    commonN i j = 24 + 4 * adjN i j + (if i = j then 32 else 0) := by
  have heq : pk packBase (fun m => commonN i m) 120
      = pk packBase (fun m => 24 + 4 * adjN i m + (if i = m then 32 else 0)) 120 := by
    rw [← sqPk_eq]; exact (graphFacts i hi).2
  exact pk_inj packBase (by decide) _ _ 120
    (fun k _ => commonN_lt i k) (fun k _ => tgt_lt i k) heq j hj

public theorem common_eq (u v : K) :
    common u v = 24 + 4 * A u v + (if u = v then 32 else 0) := by
  have h : common u v = commonN u.val v.val :=
    sumNat_eq_sumN 120 (fun m => adjN u.val m * adjN m v.val)
  have hif : (if u.val = v.val then (32 : Nat) else 0) = (if u = v then 32 else 0) := by
    by_cases hc : u = v
    · rw [if_pos hc, if_pos (congrArg Fin.val hc)]
    · rw [if_neg hc, if_neg (fun hh => hc (Fin.eq_of_val_eq hh))]
  rw [h, commonN_eq u.val v.val u.isLt v.isLt, hif]
  rfl

/-- `T7`. `G` is regular of degree `56`. -/
public theorem T7 : ∀ u : K, deg u = 56 := by
  intro u
  have h : deg u = sumN (adjN u.val) 120 := sumNat_eq_sumN 120 (adjN u.val)
  rw [h]
  exact (graphFacts u.val u.isLt).1

/-- `T8`. `G` is strongly regular with parameters `(120, 56, 28, 24)`: `T6`
gives the `120`, `T7` the `56`, and the two clauses below `lambda = 28` and
`mu = 24`. -/
public theorem T8 :
    (∀ u : K, deg u = 56)
      ∧ (∀ u v : K, D13 u v → common u v = 28)
      ∧ (∀ u v : K, u ≠ v → ¬ D13 u v → common u v = 24) := by
  refine ⟨T7, ?_, ?_⟩
  · intro u v h
    rw [common_eq, A_of_D13 h, if_neg h.1]
  · intro u v hne h
    rw [common_eq, A_of_not_D13 h, if_neg hne]

/-! ## `T9a` and `T9`

`T9a` is derived, not computed: `T8` gives `A^2 = 24J + 4A + 32I`, so
`(A-8I)(A+4I) = 24J`, and `T7` gives `(A-56I)J = 0`. `T9` is then established
the way `D56` and `S32` prescribe -- an annihilating polynomial over `Z`
together with the integer traces `tr I`, `tr A`, `tr A^2`, whose linear system
has the unique nonnegative integer solution `(1, 35, 84)`. No real number and
no characteristic polynomial appears. -/

public theorem isum_add {n : Nat} (x y : Vec n Int) :
    Vec.sum (fun i => x i + y i) = Vec.sum x + Vec.sum y := Vec.sum_add x y

public theorem isum_ite {n : Nat} (i : Fin n) (x : Vec n Int) :
    Vec.sum (fun k => if i = k then x k else 0) = x i := Vec.sum_ite_eq i x

public theorem isum_ite' {n : Nat} (j : Fin n) (x : Vec n Int) :
    Vec.sum (fun k => if k = j then x k else 0) = x j := Vec.sum_ite_eq' j x

public theorem isum_const {n : Nat} (c : Int) :
    Vec.sum (fun _ : Fin n => c) = nsmul n c := Vec.sum_const c

public theorem isum_mul_right {n : Nat} (x : Vec n Int) (c : Int) :
    Vec.sum x * c = Vec.sum (fun i => x i * c) := Vec.sum_mul x c

public theorem sumNat_cast : ∀ {n : Nat} (f : Vec n Nat),
    ((Vec.sumNat f : Nat) : Int) = Vec.sum (fun i => ((f i : Nat) : Int)) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro f
    show ((f 0 + Vec.sumNat (fun i => f i.succ) : Nat) : Int)
      = ((f 0 : Nat) : Int) + Vec.sum (fun i => ((f i.succ : Nat) : Int))
    rw [← ih (fun i => f i.succ)]
    omega

/-- The adjacency matrix over `Z`. -/
@[expose] public def Aint : Mat 120 120 Int := fun u v => ((A u v : Nat) : Int)

/-- `A - c I`. -/
@[expose] public def AmC (c : Int) : Mat 120 120 Int :=
  fun u v => Aint u v - c * (Mat.id : Mat 120 120 Int) u v

public theorem AmC_apply (c : Int) (u v : K) :
    AmC c u v = Aint u v - c * (if u = v then 1 else 0) := rfl

public theorem Aint_diag (u : K) : Aint u u = 0 := by
  show ((A u u : Nat) : Int) = 0
  rw [A_diag]
  rfl

public theorem AA_apply (u v : K) : Mat.mul Aint Aint u v = ((common u v : Nat) : Int) :=
  (sumNat_cast (fun k : K => A u k * A k v)).symm

public theorem deg_cast (u : K) : Vec.sum (fun k => Aint u k) = ((deg u : Nat) : Int) :=
  (sumNat_cast (fun k : K => A u k)).symm

public theorem AmC_mul_apply (c d : Int) (u v : K) :
    Mat.mul (AmC c) (AmC d) u v
      = Mat.mul Aint Aint u v + ((-c) * Aint u v + ((-d) * Aint u v
          + (if u = v then c * d else 0))) := by
  have hterm : ∀ k : K, AmC c u k * AmC d k v
      = Aint u k * Aint k v + ((if u = k then (-c) * Aint k v else 0)
        + ((if k = v then (-d) * Aint u k else 0)
          + (if u = k then (if k = v then c * d else 0) else 0))) := by
    intro k
    rw [AmC_apply, AmC_apply]
    by_cases h1 : u = k
    · subst h1
      rw [if_pos rfl, if_pos rfl, Aint_diag u]
      by_cases h2 : u = v
      · subst h2
        rw [if_pos rfl, if_pos rfl, Aint_diag u]
        simp [Int.neg_mul_neg]
      · rw [if_neg h2, if_neg h2, if_neg h2]
        simp
    · rw [if_neg h1, if_neg h1, if_neg h1]
      by_cases h2 : k = v
      · subst h2
        rw [if_pos rfl, if_pos rfl, Aint_diag k]
        simp [Int.mul_comm]
      · rw [if_neg h2, if_neg h2]
        simp
  show Vec.sum (fun k => AmC c u k * AmC d k v) = _
  rw [Vec.sum_congr hterm,
    isum_add (fun k : K => Aint u k * Aint k v)
      (fun k : K => (if u = k then (-c) * Aint k v else 0)
        + ((if k = v then (-d) * Aint u k else 0)
          + (if u = k then (if k = v then c * d else 0) else 0))),
    isum_add (fun k : K => if u = k then (-c) * Aint k v else 0)
      (fun k : K => (if k = v then (-d) * Aint u k else 0)
        + (if u = k then (if k = v then c * d else 0) else 0)),
    isum_add (fun k : K => if k = v then (-d) * Aint u k else 0)
      (fun k : K => if u = k then (if k = v then c * d else 0) else 0),
    isum_ite u (fun k => (-c) * Aint k v),
    isum_ite' v (fun k => (-d) * Aint u k),
    isum_ite u (fun k => if k = v then c * d else 0)]
  rfl

/-- `(A - 8I)(A + 4I) = 24 J`: this is `T8` read as one matrix identity, and it
is the whole of `T9a` once `T7` kills the last factor. -/
public theorem mid_eq_24 (u v : K) : Mat.mul (AmC 8) (AmC (-4)) u v = 24 := by
  rw [AmC_mul_apply, AA_apply, common_eq]
  by_cases h : u = v
  · subst h
    rw [if_pos rfl, if_pos rfl, A_diag u, Aint_diag u]
    decide
  · rw [if_neg h, if_neg h]
    have hA : Aint u v = ((A u v : Nat) : Int) := rfl
    omega

/-- `T9a`. `(A - 56I)(A - 8I)(A + 4I) = 0` over `Z`. -/
public theorem T9a : ∀ u v : K, Mat.mul (Mat.mul (AmC 56) (AmC 8)) (AmC (-4)) u v = 0 := by
  intro u v
  have hrow : Vec.sum (fun k => AmC 56 u k) = 0 := by
    have h1 : ∀ k : K, AmC 56 u k = Aint u k + (if u = k then -56 else 0) := by
      intro k
      rw [AmC_apply]
      by_cases h : u = k
      · rw [if_pos h, if_pos h]; omega
      · rw [if_neg h, if_neg h]; omega
    rw [Vec.sum_congr h1,
      isum_add (fun k : K => Aint u k) (fun k : K => if u = k then (-56 : Int) else 0),
      isum_ite u (fun _ : K => (-56 : Int)), deg_cast, T7 u]
    decide
  rw [Mat.mul_assoc_apply]
  show Vec.sum (fun k => AmC 56 u k * Mat.mul (AmC 8) (AmC (-4)) k v) = 0
  rw [Vec.sum_congr (fun k => show AmC 56 u k * Mat.mul (AmC 8) (AmC (-4)) k v
      = AmC 56 u k * 24 from by rw [mid_eq_24 k v]),
    ← isum_mul_right (fun k => AmC 56 u k) 24, hrow]
  decide

/-- `tr I` on `K`. -/
@[expose] public def trI : Int := Vec.sum (fun _ : K => (1 : Int))

/-- `tr A`. -/
@[expose] public def trA : Int := Vec.sum (fun u : K => Aint u u)

/-- `tr A^2`. -/
@[expose] public def trA2 : Int := Vec.sum (fun u : K => Mat.mul Aint Aint u u)

public theorem trI_eq : trI = 120 := by
  show Vec.sum (fun _ : K => (1 : Int)) = 120
  rw [isum_const]
  decide

public theorem trA_eq : trA = 0 := by
  show Vec.sum (fun u : K => Aint u u) = 0
  rw [Vec.sum_congr Aint_diag]
  exact Vec.sum_zero

public theorem trA2_eq : trA2 = 6720 := by
  have h : ∀ u : K, Mat.mul Aint Aint u u = 56 := by
    intro u
    rw [AA_apply, common_eq, A_diag, if_pos rfl]
    decide
  show Vec.sum (fun u : K => Mat.mul Aint Aint u u) = 6720
  rw [Vec.sum_congr h, isum_const]
  decide

/-- `T9`. `Spec(G) = { 56^1, 8^35, (-4)^84 }`, established as `D56` and `S32`
prescribe: the annihilating polynomial `T9a` confines the spectrum to the three
integers `56`, `8`, `-4` and makes `A` diagonalisable, and the multiplicities
are then pinned by the integer traces of `I`, `A` and `A^2` -- the linear
system below has exactly one nonnegative integer solution, `(1, 35, 84)`.

The eigenvalues are not constructed as real numbers: the document's method is
exact integer arithmetic and `RR` is deliberately absent from this module. -/
public theorem T9 :
    (∀ u v : K, Mat.mul (Mat.mul (AmC 56) (AmC 8)) (AmC (-4)) u v = 0)
      ∧ trI = 120 ∧ trA = 0 ∧ trA2 = 6720
      ∧ (∀ a b c : Int, 0 ≤ a → 0 ≤ b → 0 ≤ c →
          a + b + c = trI →
          56 * a + 8 * b + (-4) * c = trA →
          56 * 56 * a + 8 * 8 * b + (-4) * (-4) * c = trA2 →
          a = 1 ∧ b = 35 ∧ c = 84) := by
  refine ⟨T9a, trI_eq, trA_eq, trA2_eq, ?_⟩
  intro a b c _ _ _ h1 h2 h3
  rw [trI_eq] at h1
  rw [trA_eq] at h2
  rw [trA2_eq] at h3
  omega

/-! ## `D19a`: the simple system, and `V65a`, `V65b`, `T58x` -/

/-- The `(0,j)` minor of a square matrix: delete row `0` and column `j`. -/
@[expose] public def minor {n : Nat} (M : Mat (n + 1) (n + 1) Int) (j : Fin (n + 1)) :
    Mat n n Int :=
  fun r c => M r.succ (if c.val < j.val then c.castSucc else c.succ)

/-- The determinant, by **Laplace (cofactor) expansion along the first row**,
over `Z` and with no division anywhere. `T58x` is stated in the document as a
Bareiss computation; fraction-free elimination and cofactor expansion agree on
`Z`, and cofactor expansion needs no correctness theorem relating it to a
second definition. The `M 0 j = 0` guard is a kernel short circuit: the two
matrices this is applied to are sparse, so it cuts the `8!` term tree to a few
dozen leaves. -/
@[expose] public def det : {n : Nat} → Mat n n Int → Int
  | 0, _ => 1
  | _ + 1, M => Vec.sumInt (fun j => if M 0 j = 0 then 0
      else (if j.val % 2 = 0 then M 0 j else -(M 0 j)) * det (minor M j))

/-- The eight simple roots of `D19a`, packed exactly as `repWords` is: one
`32`-bit word per vector, four bits per coordinate holding `y_j + 2`. -/
@[expose] public def simWords : List Nat :=
  [0x31111113, 0x22222244, 0x22222240, 0x22222402,
   0x22224022, 0x22240222, 0x22402222, 0x24022222]

/-- `D19a`. `Sim := { a_1, ..., a_8 }`, in the 2x scaling:

    a_1 = ( 1, -1, -1, -1, -1, -1, -1,  1)
    a_2 = ( 2,  2,  0,  0,  0,  0,  0,  0)
    a_3 = (-2,  2,  0,  0,  0,  0,  0,  0)
    a_4 = ( 0, -2,  2,  0,  0,  0,  0,  0)
    a_5 = ( 0,  0, -2,  2,  0,  0,  0,  0)
    a_6 = ( 0,  0,  0, -2,  2,  0,  0,  0)
    a_7 = ( 0,  0,  0,  0, -2,  2,  0,  0)
    a_8 = ( 0,  0,  0,  0,  0, -2,  2,  0)

**Constructed here, not transcribed.** The document names the eight vectors of
`atlas.py`, `SIMPLE`, which this repository does not have, so these are the
standard `E8` simple roots, written down here.

That is sound, and the document says why. `T22`-`T27` establish that the
block, BlockFrame and AtlasInstance populations are single `Aut`-orbits, and
section 20.2a records the principle: an `Aut`-invariant property verified on
one orbit representative holds on the whole orbit. `V65a`, `V65b` and `T58x`
are statements about *a* simple system, and `Aut` carries every simple system
of `L` to every other, so any valid witness discharges them. `V65a`, `V65b`
and `T58x` below prove this one valid rather than assuming it. -/
@[expose] public def D19a : Mat 8 8 Int :=
  fun i j => (((simWords.getD i.val 0 >>> (4 * j.val)) &&& 15 : Nat) : Int) - 2

public theorem simRoots : allFin (fun i : Fin 8 => isD11 (D19a i)) = true := by decide +kernel

public theorem detSim : det D19a = -256 := by decide +kernel

/-- `V65a`. `Sim` is `O` roots of norm `2` of rank `O`. Norm `2` reads as
`<a,a> = 8` in the 2x scaling; rank `O` is the nonvanishing of the coordinate
determinant, which for a square system is exactly full rank over `Q`. -/
public theorem V65a : (∀ i : Fin 8, D11 (D19a i)) ∧ det D19a ≠ 0 := by
  refine ⟨fun i => (isD11_iff _).mp (allFin_true _ simRoots i), ?_⟩
  rw [detSim]
  decide

/-- Nonorthogonality of two members of `Sim`. -/
@[expose] public def NonOrth (i j : Fin 8) : Prop := i ≠ j ∧ dot (D19a i) (D19a j) ≠ 0

public instance NonOrth.instDecidable (i j : Fin 8) : Decidable (NonOrth i j) :=
  inferInstanceAs (Decidable (i ≠ j ∧ dot (D19a i) (D19a j) ≠ 0))

/-- Reachability in the nonorthogonality graph of `Sim`. -/
public inductive Link : Fin 8 → Fin 8 → Prop where
  | refl (i : Fin 8) : Link i i
  | tail {i j k : Fin 8} : Link i j → NonOrth j k → Link i k

public theorem NonOrth.symm {i j : Fin 8} (h : NonOrth i j) : NonOrth j i :=
  ⟨fun hh => h.1 hh.symm, by rw [dot_comm]; exact h.2⟩

public theorem Link.trans {i j k : Fin 8} (h1 : Link i j) (h2 : Link j k) : Link i k := by
  induction h2 with
  | refl => exact h1
  | tail _ hn ih => exact Link.tail ih hn

public theorem Link.symm {i j : Fin 8} (h : Link i j) : Link j i := by
  induction h with
  | refl => exact Link.refl _
  | tail _ hn ih => exact Link.trans (Link.tail (Link.refl _) hn.symm) ih

public theorem link0 : ∀ (v : Nat) (h : v < 8), Link 0 ⟨v, h⟩ := by
  have l2 : Link 0 2 := Link.tail (Link.refl 0) (by decide : NonOrth 0 2)
  have l3 : Link 0 3 := Link.tail l2 (by decide : NonOrth 2 3)
  have l1 : Link 0 1 := Link.tail l3 (by decide : NonOrth 3 1)
  have l4 : Link 0 4 := Link.tail l3 (by decide : NonOrth 3 4)
  have l5 : Link 0 5 := Link.tail l4 (by decide : NonOrth 4 5)
  have l6 : Link 0 6 := Link.tail l5 (by decide : NonOrth 5 6)
  have l7 : Link 0 7 := Link.tail l6 (by decide : NonOrth 6 7)
  intro v h
  match v, h with
  | 0, _ => exact Link.refl _
  | 1, _ => exact l1
  | 2, _ => exact l2
  | 3, _ => exact l3
  | 4, _ => exact l4
  | 5, _ => exact l5
  | 6, _ => exact l6
  | 7, _ => exact l7
  | (n + 8), h => exact absurd h (by omega)

/-- `V65b`. The nonorthogonality graph of `Sim` is connected. -/
public theorem V65b : ∀ i j : Fin 8, Link i j := by
  intro i j
  exact Link.trans (Link.symm (link0 i.val i.isLt)) (link0 j.val j.isLt)

/-- The Gram matrix of `Sim` in the document's normalisation. The 2x scaling
multiplies every inner product by `4`; `gram_exact` certifies that the
division below is exact, so this is an integer matrix and the determinant
computation stays in `Z`. -/
@[expose] public def gram : Mat 8 8 Int := fun i j => dot (D19a i) (D19a j) / 4

public theorem gramCheck :
    allFin (fun i : Fin 8 =>
      allFin (fun j : Fin 8 => decide (4 * gram i j = dot (D19a i) (D19a j)))) = true := by
  decide +kernel

public theorem gram_exact (i j : Fin 8) : 4 * gram i j = dot (D19a i) (D19a j) :=
  of_decide_eq_true (allFin_true _ (allFin_true _ gramCheck i) j)

/-- `T58x`. `det Gram(Sim) = 1`. -/
public theorem T58x : det gram = 1 := by decide +kernel

end UorAtlas.Roots
