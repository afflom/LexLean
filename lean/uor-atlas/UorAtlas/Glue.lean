module
public import Init
public import UorAtlas.Prelude.Linear

/-!
The glue lattice `L_n = D u (D + h)` of `D10`, at every dimension `n`.

`D9` and `D10` name the construction at the single dimension `O = 8`, but five
labels of `UOR-ATLAS-FORMAL-001` quantify over `n` instead: `T57a`, `T57b`,
`T57c` (section 20.5), `T84` and `T85` (section 15). Section 19.1 records all
five as `DECIDED` in Presburger arithmetic "because divisibility is by
constants". That status is about the *arithmetic side condition*; the
statements themselves are about the lattice, so they are proved here about the
lattice, with `omega` discharging the divisibility steps. `T57` itself is
retracted (section 20.1) and is deliberately absent.

## Why everything below is scaled by two

`D10` puts `L` in `(1/2)Z^n`: the glue vector is `h = (1/2, ..., 1/2)`. Doubling
every coordinate is an isomorphism onto a sublattice of `Z^n` that multiplies
the bilinear form of section 0 by exactly `4`, so nothing is lost and `Rat`
never has to enter. Under it

* `h` becomes the all-ones vector, so `h + h = (1, ..., 1)` of `P2` *is* the
  scaled glue vector;
* `D11`'s root condition `<x,x> = 2` becomes `<y,y> = 8`, which is `rootNorm`;
* `D13`'s edge condition `|<u,v>| = 1` becomes `|<u,v>| = 4`, which is
  `edgeNorm`;
* a value `v` of the unscaled form appears as the integer `4v`, so "`v` is an
  integer" reads `4 | <y,z>` and "`v` is an even integer" reads `8 | <y,y>`.

The scaling is defined once, here, and `UorAtlas/Roots.lean` consumes it: the
exported surface is `ones`, `rootNorm`, `edgeNorm`, `MemD`, `MemGlue`, `MemL`,
the congruence forms `MemDCongr`/`MemGlueCongr` with their equivalences, and
the `Decidable` instances those equivalences supply.

Membership is stated in the shape `D10` states it -- an existential over the
integer point of `D` that the element sits above -- because that is the
definition being formalised. The congruence forms exist because concrete root
data has to be *checked*, and an existential over `Vec n Int` is not decidable.
-/

set_option autoImplicit false

namespace UorAtlas.Glue

open UorAtlas.Prelude.Linear
open UorAtlas.Prelude.AddCommGroup

variable {n : Nat}

/-! ## Finite integer sums

`Linear.lean` proves the sum lemmas for the class-level `Vec.sum` over an
arbitrary `AddCommGroup`. Everything below runs on `Vec.sumInt`, which is
`Int.add` with no class projection in the way, so the six facts this module
consumes are proved directly on it rather than crossing `sumInt_eq_sum` and
back at every step. -/

public theorem sumInt_congr {x y : Vec n Int} (h : ∀ i, x i = y i) :
    Vec.sumInt x = Vec.sumInt y := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show x 0 + Vec.sumInt (fun i => x i.succ) = y 0 + Vec.sumInt (fun i => y i.succ)
    rw [h 0, ih (fun i => h i.succ)]

public theorem sumInt_add (x y : Vec n Int) :
    Vec.sumInt (fun i => x i + y i) = Vec.sumInt x + Vec.sumInt y := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show x 0 + y 0 + Vec.sumInt (fun i => x i.succ + y i.succ)
      = (x 0 + Vec.sumInt fun i => x i.succ) + (y 0 + Vec.sumInt fun i => y i.succ)
    rw [ih (fun i => x i.succ) (fun i => y i.succ)]
    omega

public theorem sumInt_mul_left (c : Int) (x : Vec n Int) :
    Vec.sumInt (fun i => c * x i) = c * Vec.sumInt x := by
  induction n with
  | zero => exact (Int.mul_zero c).symm
  | succ k ih =>
    show c * x 0 + Vec.sumInt (fun i => c * x i.succ) = c * (x 0 + Vec.sumInt fun i => x i.succ)
    rw [ih (fun i => x i.succ), Int.mul_add]

public theorem sumInt_const (c : Int) :
    Vec.sumInt (n := n) (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => exact (Int.zero_mul c).symm
  | succ k ih =>
    show c + Vec.sumInt (n := k) (fun _ => c) = ((k : Int) + 1) * c
    rw [ih, Int.add_mul, Int.one_mul, Int.add_comm]

public theorem sumInt_dvd (d : Int) (x : Vec n Int) (h : ∀ i, d ∣ x i) :
    d ∣ Vec.sumInt x := by
  induction n with
  | zero => exact Int.dvd_zero d
  | succ k ih =>
    show d ∣ x 0 + Vec.sumInt (fun i => x i.succ)
    exact Int.dvd_add (h 0) (ih (fun i => x i.succ) (fun i => h i.succ))

/-- A sum of `n` terms, each at least one, is at least `n`. This is the only
inequality the module needs, and `T85` needs it: divisibility alone leaves
`n = 0` open. -/
public theorem sumInt_ge_card (x : Vec n Int) (h : ∀ i, 1 ≤ x i) :
    (n : Int) ≤ Vec.sumInt x := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    have h0 := h 0
    have hk := ih (fun i => x i.succ) (fun i => h i.succ)
    show ((k : Int) + 1) ≤ x 0 + Vec.sumInt (fun i => x i.succ)
    omega

/-! ## The scaled ambient -/

/-- The scaled glue vector: `h + h = (1, ..., 1)` of `P2`, which is `2h`. -/
@[expose] public def ones (n : Nat) : Vec n Int := fun _ => 1

public theorem sumInt_ones : Vec.sumInt (n := n) (fun _ => (1 : Int)) = (n : Int) := by
  rw [sumInt_const, Int.mul_one]

/-- `D11`'s norm condition `<x,x> = 2` in scaled coordinates. -/
@[expose] public def rootNorm : Int := 8

/-- `D13`'s edge condition `|<u,v>| = 1` in scaled coordinates: `u` and `v` are
joined iff `dot u v` is `edgeNorm` or its negation. -/
@[expose] public def edgeNorm : Int := 4

public theorem dot_def (x y : Vec n Int) : dot x y = Vec.sumInt (fun i => x i * y i) := rfl

/-- Vector addition on `Vec n Int` is `Int.add` coordinatewise. Stated once so
that `Closed` can be phrased with the group operation of `Linear.lean` while
every proof below works in plain integer arithmetic. -/
public theorem add_apply_int (x y : Vec n Int) (i : Fin n) : add x y i = x i + y i := rfl

/-! ## The lattice

`D9` is `D := { x in Z^n : sum_i x_i = 0 (mod 2) }` and `D10` is
`L := D u (D + h)`. Doubled, `D` is the set of `2z` with `sum z` even and
`D + h` is the set of `2z + (1, ..., 1)` with the same condition on `z`. -/

/-- `2D`: the scaled form of `D9`'s `D`. -/
@[expose] public def MemD (n : Nat) (y : Vec n Int) : Prop :=
  ∃ z : Vec n Int, (2 : Int) ∣ Vec.sumInt z ∧ ∀ i, y i = 2 * z i

/-- `2(D + h) = 2D + (1, ..., 1)`: the half-integer coset of `D10`. -/
@[expose] public def MemGlue (n : Nat) (y : Vec n Int) : Prop :=
  ∃ z : Vec n Int, (2 : Int) ∣ Vec.sumInt z ∧ ∀ i, y i = 2 * z i + 1

/-- `D10`'s `L := D u (D + h)`, scaled. -/
@[expose] public def MemL (n : Nat) (y : Vec n Int) : Prop :=
  MemD n y ∨ MemGlue n y

public theorem MemL_ones (n : Nat) : MemL n (ones n) :=
  Or.inr ⟨fun _ => 0, sumInt_dvd 2 _ (fun _ => ⟨0, rfl⟩), fun _ => rfl⟩

/-! ### Decidable form

The existentials above are the definition; these congruences are the same
predicates in a form a machine can check on a concrete vector, which is what
`UorAtlas/Roots.lean` needs to certify root data. -/

/-- `MemD` as congruences: every coordinate even, and the coordinate sum
divisible by `4` -- the scaled reading of "`sum_i x_i = 0 (mod 2)`". -/
@[expose] public def MemDCongr (n : Nat) (y : Vec n Int) : Prop :=
  (∀ i, y i % 2 = 0) ∧ Vec.sumInt y % 4 = 0

/-- `MemGlue` as congruences: every coordinate odd, and the coordinate sum
congruent to `n` modulo `4`. -/
@[expose] public def MemGlueCongr (n : Nat) (y : Vec n Int) : Prop :=
  (∀ i, y i % 2 = 1) ∧ (Vec.sumInt y - (n : Int)) % 4 = 0

public theorem MemD_iff (n : Nat) (y : Vec n Int) : MemD n y ↔ MemDCongr n y := by
  constructor
  · rintro ⟨z, hz, hzi⟩
    have hs : Vec.sumInt y = 2 * Vec.sumInt z := by
      rw [← sumInt_mul_left]; exact sumInt_congr hzi
    refine ⟨fun i => ?_, by omega⟩
    have := hzi i
    omega
  · rintro ⟨hpar, hsum⟩
    have hy : ∀ i, y i = 2 * (y i / 2) := fun i => by
      have := hpar i
      exact (Int.mul_ediv_cancel' (by omega : (2 : Int) ∣ y i)).symm
    have hs : Vec.sumInt y = 2 * Vec.sumInt (fun i => y i / 2) := by
      rw [← sumInt_mul_left]; exact sumInt_congr hy
    exact ⟨fun i => y i / 2, by omega, hy⟩

public theorem MemGlue_iff (n : Nat) (y : Vec n Int) : MemGlue n y ↔ MemGlueCongr n y := by
  constructor
  · rintro ⟨z, hz, hzi⟩
    have hs : Vec.sumInt y = 2 * Vec.sumInt z + (n : Int) := by
      rw [sumInt_congr hzi, sumInt_add, sumInt_mul_left, sumInt_ones]
    refine ⟨fun i => ?_, by omega⟩
    have := hzi i
    omega
  · rintro ⟨hpar, hsum⟩
    have hy : ∀ i, y i = 2 * ((y i - 1) / 2) + 1 := fun i => by
      have := hpar i
      have hd := Int.mul_ediv_cancel' (by omega : (2 : Int) ∣ y i - 1)
      omega
    have hs : Vec.sumInt y = 2 * Vec.sumInt (fun i => (y i - 1) / 2) + (n : Int) := by
      rw [sumInt_congr hy, sumInt_add, sumInt_mul_left, sumInt_ones]
    exact ⟨fun i => (y i - 1) / 2, by omega, hy⟩

public instance instDecidableMemDCongr (n : Nat) (y : Vec n Int) : Decidable (MemDCongr n y) :=
  inferInstanceAs (Decidable ((∀ i, y i % 2 = 0) ∧ Vec.sumInt y % 4 = 0))

public instance instDecidableMemGlueCongr (n : Nat) (y : Vec n Int) :
    Decidable (MemGlueCongr n y) :=
  inferInstanceAs (Decidable ((∀ i, y i % 2 = 1) ∧ (Vec.sumInt y - (n : Int)) % 4 = 0))

public instance instDecidableMemD (n : Nat) (y : Vec n Int) : Decidable (MemD n y) :=
  decidable_of_decidable_of_iff (MemD_iff n y).symm

public instance instDecidableMemGlue (n : Nat) (y : Vec n Int) : Decidable (MemGlue n y) :=
  decidable_of_decidable_of_iff (MemGlue_iff n y).symm

public instance instDecidableMemL (n : Nat) (y : Vec n Int) : Decidable (MemL n y) :=
  inferInstanceAs (Decidable (MemD n y ∨ MemGlue n y))

/-! ## The form on the two cosets

Every arithmetic fact `T57a`-`T57c`, `T84` and `T85` rest on is one of these
three products, read off the integer point each element sits above. -/

public theorem dot_of_even_even {y z a b : Vec n Int}
    (hy : ∀ i, y i = 2 * a i) (hz : ∀ i, z i = 2 * b i) :
    dot y z = 4 * dot a b := by
  rw [dot_def, dot_def, ← sumInt_mul_left]
  exact sumInt_congr fun i => by rw [hy i, hz i]; grind

public theorem dot_of_even_odd {y z a b : Vec n Int}
    (hy : ∀ i, y i = 2 * a i) (hz : ∀ i, z i = 2 * b i + 1) :
    dot y z = 4 * dot a b + 2 * Vec.sumInt a := by
  have h : dot y z = Vec.sumInt (fun i => 4 * (a i * b i) + 2 * a i) :=
    sumInt_congr fun i => by rw [hy i, hz i]; grind
  rw [h, sumInt_add, sumInt_mul_left, sumInt_mul_left, dot_def]

public theorem dot_of_odd_odd {y z a b : Vec n Int}
    (hy : ∀ i, y i = 2 * a i + 1) (hz : ∀ i, z i = 2 * b i + 1) :
    dot y z = 4 * dot a b + 2 * Vec.sumInt a + 2 * Vec.sumInt b + (n : Int) := by
  have h : dot y z = Vec.sumInt (fun i => 4 * (a i * b i) + 2 * a i + 2 * b i + 1) :=
    sumInt_congr fun i => by rw [hy i, hz i]; grind
  rw [h, sumInt_add, sumInt_add, sumInt_add, sumInt_mul_left, sumInt_mul_left,
    sumInt_mul_left, sumInt_ones, dot_def]

/-- `D` is an even lattice: `x_i^2` and `x_i` agree modulo `2`, so the norm of a
point of `D` inherits the parity of its coordinate sum. This is why the `e = 0`
half of `T57c` costs nothing and the whole condition sits on the glue coset. -/
public theorem dot_self_even {a : Vec n Int} (ha : (2 : Int) ∣ Vec.sumInt a) :
    (2 : Int) ∣ dot a a := by
  have h : dot a a = Vec.sumInt (fun i => a i * (a i - 1)) + Vec.sumInt a := by
    rw [dot_def, ← sumInt_add]
    exact sumInt_congr fun i => by grind
  have h2 : (2 : Int) ∣ Vec.sumInt (fun i => a i * (a i - 1)) :=
    sumInt_dvd 2 _ fun i => by
      rcases (by omega : (2 : Int) ∣ a i ∨ (2 : Int) ∣ (a i - 1)) with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨k * (a i - 1), by rw [hk]; grind⟩
      · exact ⟨a i * k, by rw [hk]; grind⟩
  omega

/-- `1 <= a^2` for `a != 0`: the bound that rules `n = 0` out of `T85`. -/
public theorem one_le_mul_self {a : Int} (h : a ≠ 0) : 1 ≤ a * a := by
  have key : ∀ b : Int, 1 ≤ b → 1 ≤ b * b := by
    intro b hb
    have hbb := Int.mul_le_mul hb hb (by omega) (by omega)
    rwa [Int.one_mul] at hbb
  rcases (by omega : 1 ≤ a ∨ 1 ≤ -a) with h1 | h1
  · exact key a h1
  · have h3 := key (-a) h1
    rwa [Int.neg_mul_neg] at h3

/-! ## The three lattice properties -/

/-- `L_n` is closed under the addition of `Vec n Int`. -/
@[expose] public def Closed (n : Nat) : Prop :=
  ∀ y z : Vec n Int, MemL n y → MemL n z → MemL n (add y z)

/-- `L_n` is integral: every value of the form of section 0 on `L_n` is an
integer. Scaled, that value is `dot y z / 4`. -/
@[expose] public def Integral (n : Nat) : Prop :=
  ∀ y z : Vec n Int, MemL n y → MemL n z → (4 : Int) ∣ dot y z

/-- `L_n` is even: every norm is an even integer, i.e. `dot y y / 4` is in
`2Z`. -/
@[expose] public def Even (n : Nat) : Prop :=
  ∀ y : Vec n Int, MemL n y → (8 : Int) ∣ dot y y

/-! ## The labels -/

/-- `P1`: `glue_norm(n) = n/4` by construction.

`glue_norm(n)` is `<h,h>`; scaled it is `<2h,2h> = 4<h,h>`, so the equation
`<h,h> = n/4` is the integer equation below. -/
public theorem P1 (n : Nat) : dot (ones n) (ones n) = (n : Int) := by
  show Vec.sumInt (fun _ => (1 : Int)) = (n : Int)
  exact sumInt_ones

/-- `P2`: The coordinate sum of `h+h = (1,...,1)` is `n`.

`h + h = 2h` is exactly the scaled glue vector `ones`, so no rescaling of the
coordinate sum is involved. -/
public theorem P2 (n : Nat) : Vec.sumInt (ones n) = (n : Int) :=
  sumInt_ones

/-- `T57a`: `L_n` is additively closed iff `2 | n`. -/
public theorem T57a (n : Nat) : Closed n ↔ 2 ∣ n := by
  constructor
  · intro hc
    rcases hc (ones n) (ones n) (MemL_ones n) (MemL_ones n) with ⟨z, hz, hzi⟩ | ⟨z, hz, hzi⟩
    · have hz1 : ∀ i, z i = 1 := fun i => by
        have h : (2 : Int) = 2 * z i := hzi i
        omega
      have hs : Vec.sumInt z = (n : Int) := (sumInt_congr hz1).trans sumInt_ones
      omega
    · rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact Nat.dvd_zero 2
      · have h : (2 : Int) = 2 * z ⟨0, hpos⟩ + 1 := hzi ⟨0, hpos⟩
        omega
  · intro hn y z hy hz
    have hn' : (2 : Int) ∣ (n : Int) := by omega
    rcases hy with ⟨a, ha, hai⟩ | ⟨a, ha, hai⟩ <;> rcases hz with ⟨b, hb, hbi⟩ | ⟨b, hb, hbi⟩
    · refine Or.inl ⟨fun i => a i + b i, ?_, fun i => ?_⟩
      · rw [sumInt_add]; omega
      · rw [add_apply_int, hai i, hbi i]; grind
    · refine Or.inr ⟨fun i => a i + b i, ?_, fun i => ?_⟩
      · rw [sumInt_add]; omega
      · rw [add_apply_int, hai i, hbi i]; grind
    · refine Or.inr ⟨fun i => a i + b i, ?_, fun i => ?_⟩
      · rw [sumInt_add]; omega
      · rw [add_apply_int, hai i, hbi i]; grind
    · refine Or.inl ⟨fun i => a i + b i + 1, ?_, fun i => ?_⟩
      · rw [sumInt_add, sumInt_add, sumInt_ones]; omega
      · rw [add_apply_int, hai i, hbi i]; grind

/-- `T57b`: `L_n` is integral, hence unimodular, iff `4 | n`.

The formalised content is the integrality equivalence. "Hence unimodular" is
the document's own inference from `L_n` being an index-two overlattice of a
lattice of determinant `4`; it is a determinant computation and is not part of
this statement. -/
public theorem T57b (n : Nat) : Integral n ↔ 4 ∣ n := by
  constructor
  · intro h
    have hone := h (ones n) (ones n) (MemL_ones n) (MemL_ones n)
    rw [P1] at hone
    omega
  · intro hn y z hy hz
    have hn' : (4 : Int) ∣ (n : Int) := by omega
    rcases hy with ⟨a, ha, hai⟩ | ⟨a, ha, hai⟩ <;> rcases hz with ⟨b, hb, hbi⟩ | ⟨b, hb, hbi⟩
    · rw [dot_of_even_even hai hbi]; exact ⟨dot a b, rfl⟩
    · rw [dot_of_even_odd hai hbi]; omega
    · rw [dot_comm, dot_of_even_odd hbi hai]; omega
    · rw [dot_of_odd_odd hai hbi]; omega

/-- `T57c`: `L_n` is even unimodular iff `8 | n`, which is `D1`.

`D1` reads `admissible(n) := n > 0 and n = 0 (mod 8)`; the divisibility half is
what this supplies, and the positivity half is `D1`'s own. -/
public theorem T57c (n : Nat) : (Integral n ∧ Even n) ↔ 8 ∣ n := by
  constructor
  · rintro ⟨_, he⟩
    have hone := he (ones n) (MemL_ones n)
    rw [P1] at hone
    omega
  · intro hn
    refine ⟨(T57b n).mpr (by omega), ?_⟩
    intro y hy
    have hn' : (8 : Int) ∣ (n : Int) := by omega
    rcases hy with ⟨a, ha, hai⟩ | ⟨a, ha, hai⟩
    · have hsq := dot_self_even ha
      rw [dot_of_even_even hai hai]
      omega
    · have hsq := dot_self_even ha
      rw [dot_of_odd_odd hai hai]
      omega

/-- `T84`: `<h,h> = n/4 = 2` exactly at `n = 8`.

`<h,h> = n/4` is `P1`; scaled, the value `2` is `rootNorm`. -/
public theorem T84 (n : Nat) : dot (ones n) (ones n) = rootNorm ↔ n = 8 := by
  rw [P1]
  show (n : Int) = 8 ↔ n = 8
  omega

/-- `T85`: Half-integer roots exist only at `n = 8`.

A half-integer root is a point of the glue coset `D + h` whose norm is `2`,
which scaled is `rootNorm`. Divisibility alone leaves `n = 0` open, so the
argument also uses that a vector with every coordinate odd has norm at least
`n`. -/
public theorem T85 (n : Nat) :
    (∃ y : Vec n Int, MemGlue n y ∧ dot y y = rootNorm) ↔ n = 8 := by
  constructor
  · rintro ⟨y, ⟨a, ha, hai⟩, hyy⟩
    have hyy' : dot y y = 8 := hyy
    have hd := dot_of_odd_odd hai hai
    have hsq := dot_self_even ha
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have hzero : (0 : Int) = 8 := hyy'
      omega
    · have hge : (n : Int) ≤ dot y y := by
        rw [dot_def]
        refine sumInt_ge_card _ (fun i => ?_)
        have h1 := hai i
        exact one_le_mul_self (by omega : y i ≠ 0)
      omega
  · rintro rfl
    exact ⟨ones 8, ⟨fun _ => 0, sumInt_dvd 2 _ (fun _ => ⟨0, rfl⟩), fun _ => rfl⟩, P1 8⟩

end UorAtlas.Glue
