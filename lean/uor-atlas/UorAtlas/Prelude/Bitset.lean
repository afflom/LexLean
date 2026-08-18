module
public import Init
public import UorAtlas.Prelude.Algebra

/-!
`Nat`-backed finite sets of class indices.

UOR-ATLAS-FORMAL-001 works throughout with subsets of the `120`-element class
set `K` of `D12`: a block is `12` classes (`D16`), a BlockFrame `24` (`D46a`),
an AtlasInstance `48` (`D22a`, `T12`). `T22`-`T24` count `3150` blocks, `1575`
BlockFrames and `75600` AtlasInstances; `D14`/`D15` reduce tightness to
`deg_W(v) = |W n N(v)|`; `D60` reduces a tight pair to a column sum over
indicator vectors. Every one of those is a statement about subsets of a
`120`-element set, and deciding them in the kernel means performing set
operations tens of millions of times.

A `List Nat` or a `Nat -> Bool` makes each such operation a traversal. Lean's
kernel instead carries `Nat` as a GMP bignum and intercepts `Nat.land`,
`Nat.lor`, `Nat.xor`, `Nat.shiftLeft` and `Nat.shiftRight` on literals, so a
subset of `K` is one `Nat` and each Boolean set operation is one bignum call.
This module is that representation together with the lemmas that let later
modules *state* block, BlockFrame and AtlasInstance facts set-theoretically
while *deciding* them arithmetically. Without the lemmas the representation
proves nothing; with them, a `decide` over bignums discharges a set-theoretic
theorem.

## Measured kernel behaviour

All figures are CPU seconds of the whole `lean` process on the development
container (2 cores, heavily loaded by concurrent builds, so treat them as an
upper bound and the ratios as the real signal). Sources are in
`scratchpad/bench`; each theorem was `by decide +kernel`, so the arithmetic is
performed by the kernel and not by the elaborator, and every figure below has
the `0.5 s` process baseline subtracted.

*Which operations are accelerated.* `&&&`, `|||`, `^^^`, `<<<`, `>>>` and
`Nat.testBit` each settle a `decide` on `400000`-bit operands in under `0.1 s`.
They are therefore intercepted: the fallback is `Nat.bitwise`, a well-founded
recursion that would need one unfolding per bit. The control is `Nat.log2`,
which is *not* intercepted: `Nat.log2 (2^40000) = 40000` costs `7.9 s`, four
orders of magnitude more per bit, which is what an unaccelerated operation
looks like on this harness.

*Costs, `120`-bit operands.* One rotate-plus-mask (four bitwise operations)
costs `60 us`; `10^4` intersections plus their accumulating `^^^` cost
`0.31 s`, i.e. about `16 us` per bignum call, which is dominated by kernel
expression allocation rather than by GMP. `10^4` popcounts of `120`-bit sets
cost `26 s` with `card` below (`2.6 ms` each, about `165` bignum calls).
A `120 x 120` adjacency sweep -- `14400` intersections and `14400` popcounts of
`120`-bit rows unpacked from a single `Nat` -- costs `40 s`.

*What that means for `T22`-`T24`.* Intersection is effectively free; popcount
is the budget. The `120 x 120` sweep of `T7`/`T8` is comfortable. A `3150`-block
census that popcounts once per candidate pair is not: `card` must be called
`O(10^5)`, not `O(10^8)`, so `T22`-`T24` are reachable only through the
incremental `card_insert_of_notMem`/`card_erase_of_mem` route -- carrying a
cardinality alongside a set rather than recomputing it -- which is exactly what
those lemmas exist to license.

*The gap that remains.* A SWAR popcount (mask, shift, add, multiply on a fixed
`128`-bit width) needs about `12` bignum calls instead of `165`, and would put
`10^4` popcounts near `0.2 s`. It is not used here because proving it correct
needs bit-vector reasoning that this package cannot have: `bv_decide` is
outside `Init` and discharges through `Lean.ofReduceBool`, which the axiom
audit forbids. The table-driven `card` below is the fastest popcount whose
correctness is provable from `Init` alone.
-/

set_option autoImplicit false

-- Raised for one declaration only: `cardByte_eq_spec` checks the 256-entry
-- table by exhaustion, and the default depth of 512 does not reach 256 cases.
set_option maxRecDepth 8000

namespace UorAtlas.Prelude

/-- A finite set of `Nat` indices, carried by its characteristic bits.

A `def` rather than a `structure`: the kernel's bignum interception fires on
`Nat` literals in head position, and a constructor would put a projection
between every operation and its operands. `@[expose]` because importing
modules must be able to reduce `Bitset` operations inside `decide`. -/
@[expose] public def Bitset : Type := Nat

namespace Bitset

/-- The representation, so that witness data can be written as a literal. -/
@[expose] public def ofNat (n : Nat) : Bitset := n

/-- The underlying bignum. -/
@[expose] public def toNat (s : Bitset) : Nat := s

public instance instDecidableEq : DecidableEq Bitset := inferInstanceAs (DecidableEq Nat)

/-! ## Operations

Each is written with the `Nat.` name rather than the notation because `Bitset`
is a distinct type and carries no `OrOp`/`AndOp` instances of its own; giving it
those would let an index and a set be confused by notation, which is the bug
class the separate type exists to prevent. -/

@[expose] public def empty : Bitset := (0 : Nat)

/-- Membership is `Bool`-valued because every downstream use is a decision;
the `Membership` instance below gives the propositional reading. -/
@[expose] public def mem (s : Bitset) (i : Nat) : Bool := Nat.testBit s i

public instance instMembership : Membership Nat Bitset := ⟨fun s i => s.mem i = true⟩

public instance instDecidableMem (i : Nat) (s : Bitset) : Decidable (i ∈ s) :=
  inferInstanceAs (Decidable (s.mem i = true))

@[expose] public def singleton (i : Nat) : Bitset := Nat.shiftLeft 1 i

@[expose] public def insert (s : Bitset) (i : Nat) : Bitset := Nat.lor s (singleton i)

@[expose] public def union (s t : Bitset) : Bitset := Nat.lor s t

@[expose] public def inter (s t : Bitset) : Bitset := Nat.land s t

/-- `s ^^^ (s &&& t)` rather than `s &&& ~~~t`: `Nat` has no complement, because
the complement of a finite set of indices is infinite. -/
@[expose] public def diff (s t : Bitset) : Bitset := Nat.xor s (Nat.land s t)

@[expose] public def symmDiff (s t : Bitset) : Bitset := Nat.xor s t

@[expose] public def erase (s : Bitset) (i : Nat) : Bitset := diff s (singleton i)

@[expose] public def subset (s t : Bitset) : Bool := Nat.beq (Nat.lor s t) t

/-! ## The set-theoretic reading of each operation

These are the lemmas that make the representation usable: every one turns a
statement about bignums into the corresponding statement about members. -/

public theorem mem_def (s : Bitset) (i : Nat) : i ∈ s ↔ Nat.testBit s i = true := Iff.rfl

public theorem singleton_toNat (i : Nat) : toNat (singleton i) = 2 ^ i := by
  show Nat.shiftLeft 1 i = 2 ^ i
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul]

public theorem notMem_empty (i : Nat) : i ∉ empty := by
  show ¬ (Nat.testBit (0 : Nat) i = true)
  simp

public theorem mem_singleton (i j : Nat) : i ∈ singleton j ↔ i = j := by
  show Nat.testBit (Nat.shiftLeft 1 j) i = true ↔ _
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  simp [eq_comm]

public theorem mem_union (s t : Bitset) (i : Nat) : i ∈ union s t ↔ i ∈ s ∨ i ∈ t := by
  show Nat.testBit (Nat.lor s t) i = true ↔ (Nat.testBit s i = true ∨ Nat.testBit t i = true)
  rw [Nat.lor_eq, Nat.testBit_or]
  cases Nat.testBit s i <;> cases Nat.testBit t i <;> simp

public theorem mem_inter (s t : Bitset) (i : Nat) : i ∈ inter s t ↔ i ∈ s ∧ i ∈ t := by
  show Nat.testBit (Nat.land s t) i = true ↔ (Nat.testBit s i = true ∧ Nat.testBit t i = true)
  rw [Nat.land_eq, Nat.testBit_and]
  cases Nat.testBit s i <;> cases Nat.testBit t i <;> simp

public theorem mem_diff (s t : Bitset) (i : Nat) : i ∈ diff s t ↔ i ∈ s ∧ i ∉ t := by
  show Nat.testBit (Nat.xor s (Nat.land s t)) i = true ↔
    (Nat.testBit s i = true ∧ ¬ (Nat.testBit t i = true))
  rw [Nat.xor_eq, Nat.land_eq, Nat.testBit_xor, Nat.testBit_and]
  cases Nat.testBit s i <;> cases Nat.testBit t i <;> simp

public theorem mem_symmDiff (s t : Bitset) (i : Nat) :
    i ∈ symmDiff s t ↔ ¬ (i ∈ s ↔ i ∈ t) := by
  show Nat.testBit (Nat.xor s t) i = true ↔ ¬ (Nat.testBit s i = true ↔ Nat.testBit t i = true)
  rw [Nat.xor_eq, Nat.testBit_xor]
  cases Nat.testBit s i <;> cases Nat.testBit t i <;> simp

public theorem mem_insert (s : Bitset) (i j : Nat) : i ∈ insert s j ↔ i = j ∨ i ∈ s := by
  show Nat.testBit (Nat.lor s (singleton j)) i = true ↔ (i = j ∨ Nat.testBit s i = true)
  rw [Nat.lor_eq, Nat.testBit_or]
  have h : (Nat.testBit (singleton j) i = true) ↔ i = j := mem_singleton i j
  cases hs : Nat.testBit s i <;> cases ht : Nat.testBit (singleton j) i <;> simp_all

public theorem mem_erase (s : Bitset) (i j : Nat) : i ∈ erase s j ↔ i ≠ j ∧ i ∈ s := by
  rw [erase, mem_diff, mem_singleton]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- Extensionality: a `Bitset` is determined by its members, so a set-level
argument really does settle an equation between the underlying bignums. -/
public theorem ext {s t : Bitset} (h : ∀ i, i ∈ s ↔ i ∈ t) : s = t := by
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  have hi : (Nat.testBit s i = true) ↔ (Nat.testBit t i = true) := h i
  cases hs : Nat.testBit s i <;> cases ht : Nat.testBit t i <;> simp_all

public theorem subset_iff (s t : Bitset) : subset s t = true ↔ ∀ i, i ∈ s → i ∈ t := by
  constructor
  · intro h i hi
    have h' : Nat.lor s t = t := Nat.eq_of_beq_eq_true h
    have := congrArg (fun n => Nat.testBit n i) h'
    simp only [Nat.lor_eq, Nat.testBit_or] at this
    rw [mem_def] at hi ⊢
    rw [hi, Bool.true_or] at this
    exact this.symm
  · intro h
    have h' : Nat.lor s t = t := by
      refine Nat.eq_of_testBit_eq (fun i => ?_)
      simp only [Nat.lor_eq, Nat.testBit_or]
      cases hs : Nat.testBit s i
      · simp
      · have := h i (by rw [mem_def]; exact hs)
        rw [mem_def] at this
        simp [this]
    show Nat.beq (Nat.lor s t) t = true
    rw [h']
    simp


/-! ## Cardinality

Popcount is the one operation with no bignum primitive behind it, so it is the
one that has to be designed. Two definitions appear: `cardBit`, one bit per
step, which is the specification every set-theoretic lemma is proved against,
and `card`, one byte per step through a nibble-packed table, which is what
gets evaluated. `card_eq_cardBit` joins them, after which only `card` is used.

Both recursions are written with `Nat.rec` and a fuel argument rather than with
the equation compiler. That is not style: the equation compiler produces
`Nat.brecOn`, whose course-of-values table the kernel builds over the *fuel*,
and with the set itself as fuel one `120`-bit popcount then costs `7.9 s`
against `0.02 s` for the `Nat.rec` form -- measured, both forms in
`scratchpad/bench`. Lean's own `Nat.log2` is written the same way and for the
same reason. Passing the set as its own fuel is what makes the definitions
total without a width parameter; the `n = 0` guard is what stops the recursion
after one step per bit rather than one per unit of fuel. -/

/-- One bit per step. The specification, not the implementation. -/
@[expose] public def cardBitAux (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih n => if n = 0 then 0 else n % 2 + ih (n / 2)) fuel

/-- The argument is `Nat`, not `Bitset`: every lemma about a popcount rewrites
under `/ 2`, and `Bitset` carries no `HDiv`, so a `Bitset`-typed argument would
force the notation to elaborate at the wrong type. `Bitset` unfolds to `Nat`,
so `card s` still applies to a set. -/
@[expose] public def cardBit (n : Nat) : Nat := cardBitAux n n

public theorem cardBitAux_succ (f n : Nat) :
    cardBitAux (f + 1) n = if n = 0 then 0 else n % 2 + cardBitAux f (n / 2) := rfl

public theorem cardBitAux_zero_arg (f : Nat) : cardBitAux f 0 = 0 := by
  cases f with
  | zero => rfl
  | succ f => rw [cardBitAux_succ]; simp

/-- Any fuel at least as large as the set computes the same count. The set is
its own bound because `n / 2 < n`, so `n` steps always suffice. -/
public theorem cardBitAux_irrel : ∀ (f g n : Nat), n ≤ f → n ≤ g → cardBitAux f n = cardBitAux g n
  | 0, g, n, hf, _ => by
      have : n = 0 := Nat.le_zero.mp hf
      subst this; rw [cardBitAux_zero_arg, cardBitAux_zero_arg]
  | f + 1, 0, n, _, hg => by
      have : n = 0 := Nat.le_zero.mp hg
      subst this; rw [cardBitAux_zero_arg, cardBitAux_zero_arg]
  | f + 1, g + 1, n, hf, hg => by
      rw [cardBitAux_succ, cardBitAux_succ]
      by_cases h : n = 0
      · simp [h]
      · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
        simp only [h, if_false]
        exact congrArg _ (cardBitAux_irrel f g (n / 2) (by omega) (by omega))

public theorem cardBit_zero : cardBit 0 = 0 := rfl

/-- The defining recursion, and unconditional: at `n = 0` both sides are `0`,
so no side condition has to be carried through the lemmas below. -/
public theorem cardBit_step (n : Nat) : cardBit n = n % 2 + cardBit (n / 2) := by
  cases n with
  | zero => rfl
  | succ m =>
      show cardBitAux (m + 1) (m + 1) = (m + 1) % 2 + cardBitAux ((m + 1) / 2) ((m + 1) / 2)
      rw [cardBitAux_succ]
      simp only [Nat.succ_ne_zero, if_false]
      exact congrArg _ (cardBitAux_irrel m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _))

/-- Popcount of every byte, four bits per entry: hex digit `i` of this numeral
is the number of ones in `i`. Packing the table into one numeral is what makes
the lookup three bignum calls (`4 * c`, one shift, one mask) instead of a
structure traversal, and a `Nat` literal is the only container the kernel reads
in constant time. -/
@[expose] public def cardByteTable : Nat :=
  0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110

@[expose] public def cardByte (c : Nat) : Nat :=
  Nat.land (Nat.shiftRight cardByteTable (4 * c)) 15

/-- One byte per step. Fifteen steps cover a `120`-bit set where `cardBit`
takes `120`; measured, that is `2.6 ms` against `11 ms` per popcount. -/
@[expose] public def cardAux (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih n => if n = 0 then 0 else cardByte (n % 256) + ih (n / 256)) fuel

@[expose] public def card (n : Nat) : Nat := cardAux n n

/-- The low eight bits of `c`, summed. Stated as an explicit sum rather than as
`cardBit (c % 256)` so that every step of the bridge below is division and
remainder by *literals*, which is exactly what `omega` decides. -/
@[expose] public def cardByteSpec (c : Nat) : Nat :=
  c % 2 + c / 2 % 2 + c / 4 % 2 + c / 8 % 2 + c / 16 % 2 + c / 32 % 2 + c / 64 % 2 + c / 128 % 2

public theorem cardAux_succ (f n : Nat) :
    cardAux (f + 1) n = if n = 0 then 0 else cardByte (n % 256) + cardAux f (n / 256) := rfl

/-- The table is correct, by exhaustion over its `256` entries. -/
public theorem cardByte_eq_spec : ∀ c, c < 256 → cardByte c = cardByteSpec c := by decide

/-- Eight steps of `cardBit_step`, collected. -/
public theorem cardBit_step_byte (n : Nat) : cardBit n = cardByteSpec n + cardBit (n / 256) := by
  rw [cardBit_step n, cardBit_step (n / 2), cardBit_step (n / 2 / 2), cardBit_step (n / 2 / 2 / 2),
    cardBit_step (n / 2 / 2 / 2 / 2), cardBit_step (n / 2 / 2 / 2 / 2 / 2),
    cardBit_step (n / 2 / 2 / 2 / 2 / 2 / 2), cardBit_step (n / 2 / 2 / 2 / 2 / 2 / 2 / 2)]
  simp only [Nat.div_div_eq_div_mul, Nat.reduceMul, cardByteSpec]
  omega

public theorem cardAux_eq : ∀ (f n : Nat), n ≤ f → cardAux f n = cardBit n
  | 0, n, h => by
      have hn : n = 0 := Nat.le_zero.mp h
      subst hn; rfl
  | f + 1, n, h => by
      rw [cardAux_succ]
      by_cases hn : n = 0
      · subst hn; rw [if_pos rfl, cardBit_zero]
      · have hlt : n / 256 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
        have hmod : cardByteSpec (n % 256) = cardByteSpec n := by
          simp only [cardByteSpec]; omega
        simp only [hn, if_false]
        rw [cardAux_eq f (n / 256) (by omega), cardByte_eq_spec (n % 256) (Nat.mod_lt _ (by decide)),
          hmod, cardBit_step_byte n]

/-- The table-driven count and the specification agree on every set. -/
public theorem card_eq_cardBit (n : Nat) : card n = cardBit n :=
  cardAux_eq n n (Nat.le_refl n)

public theorem card_empty : card empty = 0 := rfl

public theorem card_step (n : Nat) : card n = n % 2 + card (n / 2) := by
  rw [card_eq_cardBit, card_eq_cardBit, cardBit_step]

/-! ## Cardinality as a set invariant

The lemmas below are what the representation is for. `card_insert_of_notMem`
and `card_erase_of_mem` in particular let an enumeration carry a cardinality
alongside a set instead of recomputing a popcount, which the measurements above
show is the difference between `T22`-`T24` being reachable and not. -/

/-- Recursion on the binary representation of two sets at once. Well-founded
recursion is fine here because it is a *proof*, never reduced by the kernel;
the definitions above may not use it, and do not. -/
public theorem bitInduction {P : Nat → Nat → Prop} (hz : P 0 0)
    (hs : ∀ a b, ¬ (a = 0 ∧ b = 0) → P (a / 2) (b / 2) → P a b) : ∀ a b, P a b := by
  have aux : ∀ n a b, a + b ≤ n → P a b := by
    intro n
    induction n with
    | zero =>
        intro a b h
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha; subst hb; exact hz
    | succ n ih =>
        intro a b h
        by_cases h0 : a = 0 ∧ b = 0
        · rw [h0.1, h0.2]; exact hz
        · exact hs a b h0 (ih _ _ (by omega))
  exact fun a b => aux (a + b) a b (Nat.le_refl _)

public theorem card_eq_zero (n : Nat) : card n = 0 ↔ n = 0 := by
  refine bitInduction (P := fun a _ => card a = 0 ↔ a = 0) ?_ ?_ n 0
  · exact ⟨fun _ => rfl, fun _ => card_empty⟩
  · intro a b _ ih
    constructor
    · intro h
      rw [card_step a] at h
      have h1 : a % 2 = 0 := by omega
      have h2 : a / 2 = 0 := ih.mp (by omega)
      omega
    · intro h; subst h; exact card_empty

/-- Setting a bit that was clear adds exactly one to the count. -/
public theorem card_lor_two_pow :
    ∀ (i n : Nat), Nat.testBit n i = false → card (Nat.lor n (2 ^ i)) = card n + 1
  | 0, n, h => by
      have hn : n % 2 = 0 := Nat.mod_two_eq_zero_iff_testBit_zero.mpr h
      have hor : (Nat.lor n (2 ^ 0)) % 2 = 1 := by
        rw [Nat.lor_eq]
        exact Nat.or_mod_two_eq_one.mpr (Or.inr (by decide))
      have hdiv : (Nat.lor n (2 ^ 0)) / 2 = n / 2 := by
        rw [Nat.lor_eq, Nat.or_div_two]
        simp
      rw [card_step (Nat.lor n (2 ^ 0)), card_step n, hor, hdiv, hn]
      omega
  | i + 1, n, h => by
      have hp : (2 : Nat) ^ (i + 1) = 2 ^ i * 2 := Nat.pow_succ 2 i
      have hmod : (2 : Nat) ^ (i + 1) % 2 = 0 := by rw [hp]; exact Nat.mul_mod_left _ _
      have hhalf : (2 : Nat) ^ (i + 1) / 2 = 2 ^ i := by
        rw [hp]; exact Nat.mul_div_cancel _ (by decide)
      have hor : (Nat.lor n (2 ^ (i + 1))) % 2 = n % 2 := by
        have h1 : (n ||| 2 ^ (i + 1)) % 2 = 1 ↔ (n % 2 = 1 ∨ 2 ^ (i + 1) % 2 = 1) :=
          Nat.or_mod_two_eq_one
        have h2 := Nat.mod_two_eq_zero_or_one (n ||| 2 ^ (i + 1))
        have h3 := Nat.mod_two_eq_zero_or_one n
        rw [Nat.lor_eq]
        omega
      have hdiv : (Nat.lor n (2 ^ (i + 1))) / 2 = Nat.lor (n / 2) (2 ^ i) := by
        rw [Nat.lor_eq, Nat.or_div_two, hhalf, Nat.lor_eq]
      have hbit : Nat.testBit (n / 2) i = false := by rw [Nat.testBit_div_two]; exact h
      rw [card_step (Nat.lor n (2 ^ (i + 1))), card_step n, hor, hdiv,
        card_lor_two_pow i (n / 2) hbit]
      omega

public theorem card_singleton (i : Nat) : card (singleton i) = 1 := by
  show card (Nat.shiftLeft 1 i) = 1
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul]
  have := card_lor_two_pow i 0 (by simp)
  rw [Nat.lor_eq, Nat.zero_or] at this
  exact this

public theorem card_insert_of_notMem (s : Bitset) (i : Nat) (h : i ∉ s) :
    card (insert s i) = card s + 1 := by
  have hb : Nat.testBit s i = false := by
    cases hx : Nat.testBit s i
    · rfl
    · exact absurd hx h
  show card (Nat.lor s (Nat.shiftLeft 1 i)) = card s + 1
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul]
  exact card_lor_two_pow i s hb

public theorem insert_erase_of_mem (s : Bitset) (i : Nat) (h : i ∈ s) : insert (erase s i) i = s := by
  refine ext (fun j => ?_)
  rw [mem_insert, mem_erase]
  constructor
  · rintro (rfl | ⟨_, hj⟩)
    · exact h
    · exact hj
  · intro hj
    by_cases hij : j = i
    · exact Or.inl hij
    · exact Or.inr ⟨hij, hj⟩

public theorem card_erase_of_mem (s : Bitset) (i : Nat) (h : i ∈ s) :
    card (erase s i) + 1 = card s := by
  have hne : i ∉ erase s i := by
    rw [mem_erase]
    exact fun hc => hc.1 rfl
  have := card_insert_of_notMem (erase s i) i hne
  rw [insert_erase_of_mem s i h] at this
  exact this.symm

/-- Inclusion-exclusion, the two-set identity every counting argument in
sections 4 and 6 of the document reduces to. -/
public theorem card_union_add_card_inter (s t : Bitset) :
    card (union s t) + card (inter s t) = card s + card t := by
  refine bitInduction (P := fun a b => card (Nat.lor a b) + card (Nat.land a b) = card a + card b)
    ?_ ?_ s t
  · decide
  · intro a b _ ih
    have hmod : (Nat.lor a b) % 2 + (Nat.land a b) % 2 = a % 2 + b % 2 := by
      have h1 : (a ||| b) % 2 = 1 ↔ (a % 2 = 1 ∨ b % 2 = 1) := Nat.or_mod_two_eq_one
      have h2 : (a &&& b) % 2 = 1 ↔ (a % 2 = 1 ∧ b % 2 = 1) := Nat.and_mod_two_eq_one
      have h3 := Nat.mod_two_eq_zero_or_one (a ||| b)
      have h4 := Nat.mod_two_eq_zero_or_one (a &&& b)
      have h5 := Nat.mod_two_eq_zero_or_one a
      have h6 := Nat.mod_two_eq_zero_or_one b
      rw [Nat.lor_eq, Nat.land_eq]
      omega
    have hor : (Nat.lor a b) / 2 = Nat.lor (a / 2) (b / 2) := by
      rw [Nat.lor_eq, Nat.or_div_two, Nat.lor_eq]
    have hand : (Nat.land a b) / 2 = Nat.land (a / 2) (b / 2) := by
      rw [Nat.land_eq, Nat.and_div_two, Nat.land_eq]
    rw [card_step (Nat.lor a b), card_step (Nat.land a b), card_step a, card_step b,
      hor, hand]
    omega

public theorem card_le_of_subset {s t : Bitset} (h : subset s t = true) : card s ≤ card t := by
  have key : ∀ a b : Nat, Nat.lor a b = b → card a ≤ card b := by
    refine bitInduction (P := fun a b => Nat.lor a b = b → card a ≤ card b) ?_ ?_
    · intro _; exact Nat.le_refl _
    · intro a b _ ih hab
      have hdiv : Nat.lor (a / 2) (b / 2) = b / 2 := by
        have := congrArg (fun n => n / 2) hab
        simpa [Nat.lor_eq, Nat.or_div_two] using this
      have hmod : a % 2 ≤ b % 2 := by
        have h1 : (a ||| b) % 2 = 1 ↔ (a % 2 = 1 ∨ b % 2 = 1) := Nat.or_mod_two_eq_one
        have h2 : Nat.lor a b % 2 = b % 2 := by rw [hab]
        have h5 := Nat.mod_two_eq_zero_or_one a
        have h6 := Nat.mod_two_eq_zero_or_one b
        rw [Nat.lor_eq] at h2
        omega
      have := ih hdiv
      rw [card_step a, card_step b]
      omega
  exact key s t (Nat.eq_of_beq_eq_true h)

/-! ## Enumerating the members

`toList` is the bridge from the bignum to anything that has to iterate: a fold
over a set is `List.foldl` over `toList`. It is written with the same fuelled
`Nat.rec` as `card`, for the same reason, and it emits indices in increasing
order because that is what makes `mem_toList` a statement about `testBit`
rather than about a permutation. -/

@[expose] public def toListAux (fuel : Nat) : Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat) (fun _ _ => [])
    (fun _ ih n i =>
      if n = 0 then [] else if n % 2 = 1 then i :: ih (n / 2) (i + 1) else ih (n / 2) (i + 1)) fuel

/-- The members of `n`, each shifted up by `i`. The offset is what lets the
recursion report absolute indices while descending through `n / 2`. -/
@[expose] public def toListFrom (n : Nat) (i : Nat) : List Nat := toListAux n n i

@[expose] public def toList (s : Bitset) : List Nat := toListFrom s 0

public theorem toListAux_succ (f n i : Nat) :
    toListAux (f + 1) n i =
      if n = 0 then [] else
        if n % 2 = 1 then i :: toListAux f (n / 2) (i + 1) else toListAux f (n / 2) (i + 1) := rfl

public theorem toListAux_zero_arg (f i : Nat) : toListAux f 0 i = [] := by
  cases f with
  | zero => rfl
  | succ f => rw [toListAux_succ]; simp

public theorem toListAux_irrel :
    ∀ (f g n i : Nat), n ≤ f → n ≤ g → toListAux f n i = toListAux g n i
  | 0, g, n, i, hf, _ => by
      have hn : n = 0 := Nat.le_zero.mp hf
      subst hn; rw [toListAux_zero_arg, toListAux_zero_arg]
  | f + 1, 0, n, i, _, hg => by
      have hn : n = 0 := Nat.le_zero.mp hg
      subst hn; rw [toListAux_zero_arg, toListAux_zero_arg]
  | f + 1, g + 1, n, i, hf, hg => by
      rw [toListAux_succ, toListAux_succ]
      by_cases h : n = 0
      · simp [h]
      · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
        rw [toListAux_irrel f g (n / 2) (i + 1) (by omega) (by omega)]

public theorem toListFrom_step (n i : Nat) :
    toListFrom n i =
      if n = 0 then [] else
        if n % 2 = 1 then i :: toListFrom (n / 2) (i + 1) else toListFrom (n / 2) (i + 1) := by
  cases n with
  | zero => rfl
  | succ m =>
      show toListAux (m + 1) (m + 1) i = _
      rw [toListAux_succ]
      simp only [Nat.succ_ne_zero, if_false]
      have hirr : toListAux m ((m + 1) / 2) (i + 1) = toListFrom ((m + 1) / 2) (i + 1) :=
        toListAux_irrel m ((m + 1) / 2) ((m + 1) / 2) (i + 1) (by omega) (Nat.le_refl _)
      rw [hirr]

/-- Recursion on the binary representation of a single set. -/
public theorem bitInduction₁ {P : Nat → Prop} (hz : P 0) (hs : ∀ a, a ≠ 0 → P (a / 2) → P a) :
    ∀ a, P a := by
  have aux : ∀ n a, a ≤ n → P a := by
    intro n
    induction n with
    | zero => intro a h; have : a = 0 := by omega
              subst this; exact hz
    | succ n ih =>
        intro a h
        by_cases h0 : a = 0
        · subst h0; exact hz
        · exact hs a h0 (ih _ (by omega))
  exact fun a => aux a a (Nat.le_refl _)

public theorem le_of_mem_toListFrom : ∀ (n i j : Nat), j ∈ toListFrom n i → i ≤ j := by
  refine bitInduction₁ (P := fun n => ∀ i j, j ∈ toListFrom n i → i ≤ j) ?_ ?_
  · intro i j hj; rw [toListFrom_step] at hj; simp at hj
  · intro a ha ih i j hj
    rw [toListFrom_step, if_neg ha] at hj
    by_cases hp : a % 2 = 1
    · rw [if_pos hp, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (ih (i + 1) j hj)
    · rw [if_neg hp] at hj
      exact Nat.le_of_succ_le (ih (i + 1) j hj)

public theorem mem_toListFrom :
    ∀ (n i k : Nat), (i + k) ∈ toListFrom n i ↔ Nat.testBit n k = true := by
  refine bitInduction₁ (P := fun n => ∀ i k, (i + k) ∈ toListFrom n i ↔ Nat.testBit n k = true)
    ?_ ?_
  · intro i k
    rw [toListFrom_step]
    simp
  · intro a ha ih i k
    rw [toListFrom_step, if_neg ha]
    cases k with
    | zero =>
        have hbit : Nat.testBit a 0 = decide (a % 2 = 1) := by
          simp [Nat.testBit_zero]
        by_cases hp : a % 2 = 1
        · rw [if_pos hp, List.mem_cons]
          simp [hbit, hp]
        · rw [if_neg hp, hbit]
          constructor
          · intro hmem
            have := le_of_mem_toListFrom (a / 2) (i + 1) (i + 0) hmem
            omega
          · intro hc; simp [hp] at hc
    | succ m =>
        have hshift : Nat.testBit a (m + 1) = Nat.testBit (a / 2) m :=
          (Nat.testBit_div_two a m).symm ▸ rfl
        have hidx : i + (m + 1) = (i + 1) + m := by omega
        by_cases hp : a % 2 = 1
        · rw [if_pos hp, List.mem_cons, hidx, hshift, ih (i + 1) m]
          exact ⟨fun h => h.elim (fun hc => absurd hc (by omega)) id, Or.inr⟩
        · rw [if_neg hp, hidx, hshift, ih (i + 1) m]
    
public theorem mem_toList (s : Bitset) (k : Nat) : k ∈ toList s ↔ k ∈ s := by
  have h := mem_toListFrom s 0 k
  rw [Nat.zero_add] at h
  exact h

public theorem length_toListFrom : ∀ (n i : Nat), (toListFrom n i).length = card n := by
  refine bitInduction₁ (P := fun n => ∀ i, (toListFrom n i).length = card n) ?_ ?_
  · intro i; rw [toListFrom_step, if_pos rfl]; exact card_empty.symm
  · intro a ha ih i
    rw [toListFrom_step, if_neg ha, card_step a]
    by_cases hp : a % 2 = 1
    · rw [if_pos hp, List.length_cons, ih (i + 1), hp]
      omega
    · have hp' : a % 2 = 0 := by omega
      rw [if_neg hp, ih (i + 1), hp']
      omega

public theorem length_toList (s : Bitset) : (toList s).length = card s := length_toListFrom s 0

/-- Symmetric difference is the one of the six operations above that is a group
law, and recording it makes `Bitset` an object of the hierarchy
`UorAtlas.Prelude.Algebra` sets up rather than a bare `Nat`: the indicator
arithmetic `D60` performs on BlockFrames is addition in this group. -/
public instance instAddCommGroup : AddCommGroup Bitset where
  zero := empty
  add := symmDiff
  neg := fun s => s
  add_assoc := fun a b c => Nat.xor_assoc a b c
  add_comm := fun a b => Nat.xor_comm a b
  add_zero := fun a => Nat.xor_zero a
  add_neg := fun a => Nat.xor_self a

end Bitset

end UorAtlas.Prelude
