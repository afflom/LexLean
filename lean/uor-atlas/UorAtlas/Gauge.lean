module

public import Init
public import UorAtlas.Prelude.Algebra
public import UorAtlas.Prelude.Linear
public import UorAtlas.Prelude.Bitset
public import UorAtlas.Prelude.Perm
public import UorAtlas.Roots
public import UorAtlas.Blocks
public import UorAtlas.Group

/-!
# Section 10: the Atlas gauge group

`D28` to `D30` name the gauge group of an AtlasInstance, its action on the four
blocks, the kernel of that action, and the automorphism group of a single
block. `D21a` is section 5's componentwise action, which is what `Stab_Aut(A)`
in section 7 is a stabiliser *for*, so it lives here beside the stabiliser it
defines rather than in `Group`.

The document defines these four objects and then states `T49` to `T56` about
them. This module carries the definitions and the facts about them that follow
from the definitions alone. The *orders* -- `|Gauge(W)| = 4608`, `|Ker| = 576`,
`|image(rho)| = 8` -- are census results and are not asserted here; a
declaration that named one of those labels without a census behind it would be
a label on an unproved statement, which `R2` forbids.

Two things make this module possible without the census. First, a group is
named by a *predicate* on `Perm 120` and never by a carrier list: `Aut` has
`348364800` elements and no list of them can exist, but `D21 g` is a decidable-
free `Prop` that costs nothing to state. Second, `rho` is total by
construction rather than partial-and-then-justified: it is read off the
presentation, and `rho_perm` is the theorem that on the stabiliser it lands in
`Sym(4)`.
-/

public section

namespace UorAtlas.Gauge

open UorAtlas.Prelude
open UorAtlas.Prelude.AddCommGroup
open UorAtlas.Prelude.CommRing
open UorAtlas.Prelude.Linear
open UorAtlas.Prelude.NumInstances
open UorAtlas.Roots
open UorAtlas.Blocks
open UorAtlas.Group

/-! ## The action of a permutation of classes on a set of classes -/

/-- The image of a class set under a permutation of `K`. Written as a fold over
the `120` class indices so that it is a closed `Bitset` computation: the kernel
evaluates it without unfolding any `Perm` field beyond `toFun`. -/
@[expose] public def imgSet (g : Perm 120) (S : Bitset) : Bitset :=
  (List.finRange 120).foldl
    (fun acc i => if i.val ∈ S then Bitset.insert acc (g.toFun i).val else acc) Bitset.empty

public theorem mem_imgSet_aux (g : Perm 120) (S : Bitset) (l : List (Fin 120)) (init : Bitset)
    (j : Nat) :
    j ∈ l.foldl (fun acc i => if i.val ∈ S then Bitset.insert acc (g.toFun i).val else acc) init
      ↔ j ∈ init ∨ ∃ i ∈ l, i.val ∈ S ∧ (g.toFun i).val = j := by
  induction l generalizing init with
  | nil => exact ⟨fun h => Or.inl h, fun h => h.elim id (fun ⟨_, hi, _⟩ => absurd hi (by simp))⟩
  | cons a t ih =>
    rw [List.foldl_cons, ih]
    by_cases ha : a.val ∈ S
    · rw [if_pos ha, Bitset.mem_insert]
      constructor
      · rintro (h | h)
        · rcases h with h | h
          · exact Or.inr ⟨a, List.mem_cons_self, ha, h.symm⟩
          · exact Or.inl h
        · obtain ⟨i, hi, hs, he⟩ := h
          exact Or.inr ⟨i, List.mem_cons_of_mem _ hi, hs, he⟩
      · rintro (h | ⟨i, hi, hs, he⟩)
        · exact Or.inl (Or.inr h)
        · rcases List.mem_cons.mp hi with rfl | hi
          · exact Or.inl (Or.inl he.symm)
          · exact Or.inr ⟨i, hi, hs, he⟩
    · rw [if_neg ha]
      constructor
      · rintro (h | ⟨i, hi, hs, he⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, List.mem_cons_of_mem _ hi, hs, he⟩
      · rintro (h | ⟨i, hi, hs, he⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hi with rfl | hi
          · exact absurd hs ha
          · exact Or.inr ⟨i, hi, hs, he⟩

/-- Membership in the image is the expected one: `j` is in `g . S` exactly when
some member of `S` is carried to `j`. -/
public theorem mem_imgSet (g : Perm 120) (S : Bitset) (j : Nat) :
    j ∈ imgSet g S ↔ ∃ i : Fin 120, i.val ∈ S ∧ (g.toFun i).val = j := by
  rw [imgSet, mem_imgSet_aux]
  constructor
  · rintro (h | ⟨i, _, hs, he⟩)
    · exact absurd h (Bitset.notMem_empty j)
    · exact ⟨i, hs, he⟩
  · rintro ⟨i, hs, he⟩
    exact Or.inr ⟨i, List.mem_finRange i, hs, he⟩

/-- The image of a class set is a class set. -/
public theorem classSet_imgSet (g : Perm 120) (S : Bitset) : ClassSet (imgSet g S) := by
  show Bitset.toNat (imgSet g S) < 2 ^ 120
  refine Nat.lt_pow_two_of_testBit _ (fun i hi => ?_)
  have hno : ¬ (i ∈ imgSet g S) := by
    intro hm
    obtain ⟨k, _, he⟩ := (mem_imgSet g S i).mp hm
    exact absurd (he ▸ (g.toFun k).isLt) (by omega)
  exact Bool.not_eq_true _ |>.mp hno

/-- The identity acts trivially. -/
public theorem imgSet_one {S : Bitset} (hS : ClassSet S) : imgSet (Perm.one 120) S = S := by
  refine Bitset.ext (fun j => ?_)
  rw [mem_imgSet]
  exact ⟨fun ⟨i, hs, he⟩ => he ▸ hs, fun hj => ⟨⟨j, lt_of_mem hS hj⟩, hj, rfl⟩⟩

/-- The action is an action: images compose. -/
public theorem imgSet_comp (g h : Perm 120) (S : Bitset) :
    imgSet (g.comp h) S = imgSet g (imgSet h S) := by
  refine Bitset.ext (fun j => ?_)
  rw [mem_imgSet, mem_imgSet]
  constructor
  · rintro ⟨i, hs, he⟩
    exact ⟨h.toFun i, (mem_imgSet h S _).mpr ⟨i, hs, rfl⟩, he⟩
  · rintro ⟨i, hi, he⟩
    obtain ⟨k, hk, hke⟩ := (mem_imgSet h S _).mp hi
    exact ⟨k, hk, by
      show (g.toFun (h.toFun k)).val = j
      rw [Fin.eq_of_val_eq hke]; exact he⟩

/-- Acting by `g` and then by `g` inverse returns the set. -/
public theorem imgSet_inv (g : Perm 120) {S : Bitset} (hS : ClassSet S) :
    imgSet g.inv (imgSet g S) = S := by
  rw [← imgSet_comp]
  refine Bitset.ext (fun j => ?_)
  rw [mem_imgSet]
  constructor
  · rintro ⟨i, hs, he⟩
    have : (g.inv.comp g).toFun i = i := by
      show g.invFun (g.toFun i) = i
      exact g.left_inv i
    rw [this] at he
    exact he ▸ hs
  · intro hj
    refine ⟨⟨j, lt_of_mem hS hj⟩, hj, ?_⟩
    show (g.invFun (g.toFun ⟨j, lt_of_mem hS hj⟩)).val = j
    rw [g.left_inv]

/-! ## `D21a`: the componentwise action on AtlasPresentations

The document's `Stab_Aut(A)` is a stabiliser for *this* action, so the action
has to exist before the stabiliser can be named. `D21a` bundles the two
commuting actions and the stabiliser, as the document does. -/

/-- `Aut` acting componentwise on the blocks of a presentation. This is
well typed only once the images are again blocks, which `imgSet` alone does not
give; `actPres` is therefore the raw componentwise map on the block tuple, and
`D21a_stab` below is the stabiliser statement that consumes it. -/
@[expose] public def actPres (g : Perm 120) (b : Fin 4 → Bitset) : Fin 4 → Bitset :=
  fun a => imgSet g (b a)

/-- `Sym(4)` acting by reindexing, `sigma . (B_0,...,B_3) := (B_{sigma^-1(0)},...)`. -/
@[expose] public def reindex (s : Perm 4) (b : Fin 4 → Bitset) : Fin 4 → Bitset :=
  fun a => b (s.invFun a)

/-- `Stab_Aut(A) := { g in Aut : gB_i = B_i for every i }`, the stabiliser of an
AtlasPresentation under the componentwise action. Note this fixes every block
*separately*; `D28` below fixes only the union. -/
@[expose] public def stabPres (b : Fin 4 → Bitset) (g : Perm 120) : Prop :=
  D21 g ∧ ∀ a : Fin 4, imgSet g (b a) = b a

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
  funext (fun a => imgSet_comp g h (b a))

/-- A presentation's stabiliser is a subgroup: it contains the identity and is
closed under composition and inverse. -/
public theorem stabPres_subgroup {b : Fin 4 → Bitset} (hb : ∀ a, ClassSet (b a)) :
    stabPres b (Perm.one 120)
      ∧ (∀ g h, stabPres b g → stabPres b h → stabPres b (g.comp h))
      ∧ (∀ g, stabPres b g → stabPres b g.inv) := by
  refine ⟨⟨D21_subgroup.2.1, fun a => imgSet_one (hb a)⟩, ?_, ?_⟩
  · rintro g h ⟨hg, hgs⟩ ⟨hh, hhs⟩
    exact ⟨D21_subgroup.2.2.1 g h hg hh, fun a => by rw [imgSet_comp, hhs a, hgs a]⟩
  · rintro g ⟨hg, hgs⟩
    refine ⟨D21_subgroup.2.2.2 g hg, fun a => ?_⟩
    have := imgSet_inv g (hb a)
    rwa [hgs a] at this

/-! ## `D28`, `D28a`, `D29`: the gauge group and its block action -/

/-- `D28`. `Gauge(W) := Stab_Aut(W)`, the gauge group of an instance: the
elements of `Aut` carrying the class set `W` to itself.

The document warns that this must not be written `Aut(Atlas)`, because by `T46`
the categorical object has exactly one endomorphism. The two are different
objects and this library keeps them apart by construction: `Gauge` is a
predicate on `Perm 120`, while the categorical endomorphism monoid lives in
`Category` over `AtlasAction` and shares no declaration with it. -/
@[expose] public def D28 (W : Bitset) (g : Perm 120) : Prop :=
  D21 g ∧ imgSet g W = W

/-- `Gauge(W)` is a subgroup of `Aut`. -/
public theorem D28_subgroup {W : Bitset} (hW : ClassSet W) :
    D28 W (Perm.one 120)
      ∧ (∀ g h, D28 W g → D28 W h → D28 W (g.comp h))
      ∧ (∀ g, D28 W g → D28 W g.inv) := by
  refine ⟨⟨D21_subgroup.2.1, imgSet_one hW⟩, ?_, ?_⟩
  · rintro g h ⟨hg, hgs⟩ ⟨hh, hhs⟩
    exact ⟨D21_subgroup.2.2.1 g h hg hh, by rw [imgSet_comp, hhs, hgs]⟩
  · rintro g ⟨hg, hgs⟩
    refine ⟨D21_subgroup.2.2.2 g hg, ?_⟩
    have := imgSet_inv g hW
    rwa [hgs] at this

/-- Membership in a four-fold union, which `union4` does not come with. -/
public theorem mem_union4 (b : Fin 4 → Bitset) (j : Nat) :
    j ∈ union4 b ↔ ∃ a : Fin 4, j ∈ b a := by
  rw [union4, Bitset.mem_union, Bitset.mem_union, Bitset.mem_union]
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
    D28 (union4 b) g := by
  refine ⟨h.1, Bitset.ext (fun j => ?_)⟩
  rw [mem_imgSet]
  constructor
  · rintro ⟨i, hi, he⟩
    obtain ⟨a, ha⟩ := (mem_union4 b i.val).mp hi
    refine (mem_union4 b j).mpr ⟨a, ?_⟩
    rw [← h.2 a, mem_imgSet]
    exact ⟨i, ha, he⟩
  · intro hj
    obtain ⟨a, ha⟩ := (mem_union4 b j).mp hj
    rw [← h.2 a, mem_imgSet] at ha
    obtain ⟨i, hi, he⟩ := ha
    exact ⟨i, (mem_union4 b i.val).mpr ⟨a, hi⟩, he⟩

/-- The index of the block a gauge element sends block `a` to, read off the
presentation. Total by construction: it returns `a` itself when no block
matches, and `rho_perm` is the theorem that on the gauge group the fallback
never fires. -/
@[expose] public def rhoIdx (b : Fin 4 → Bitset) (g : Perm 120) (a : Fin 4) : Fin 4 :=
  if imgSet g (b a) = b 0 then 0
  else if imgSet g (b a) = b 1 then 1
  else if imgSet g (b a) = b 2 then 2
  else if imgSet g (b a) = b 3 then 3
  else a

/-- `rhoIdx` names the block it says it names, whenever `g` permutes the
blocks at all. -/
public theorem rhoIdx_spec {b : Fin 4 → Bitset} {g : Perm 120} {a : Fin 4}
    (h : ∃ c : Fin 4, imgSet g (b a) = b c) : imgSet g (b a) = b (rhoIdx b g a) := by
  obtain ⟨c, hc⟩ := h
  rw [rhoIdx]
  by_cases h0 : imgSet g (b a) = b 0
  · rw [if_pos h0]; exact h0
  · rw [if_neg h0]
    by_cases h1 : imgSet g (b a) = b 1
    · rw [if_pos h1]; exact h1
    · rw [if_neg h1]
      by_cases h2 : imgSet g (b a) = b 2
      · rw [if_pos h2]; exact h2
      · rw [if_neg h2]
        by_cases h3 : imgSet g (b a) = b 3
        · rw [if_pos h3]; exact h3
        · rw [if_neg h3]
          exact absurd hc (by
            match c with
            | 0 => exact h0
            | 1 => exact h1
            | 2 => exact h2
            | 3 => exact h3)

/-- `D28a`. `rho : Gauge(W) -> Sym(4)` is the action on the four blocks of `W`.

The document notes it is well defined by `T26` -- that the four blocks are
determined by `W`. This library makes the dependence explicit instead of
implicit: `rho` is a function of the presentation `b`, and `T26` is what says
the presentation is recoverable from `W`. Stating it this way means `rho`
exists before `T26` is available, and `T26` upgrades it from "the action on
this presentation" to "the action on `W`'s blocks" rather than being needed to
make it well formed. -/
@[expose] public def D28a (b : Fin 4 → Bitset) (g : Perm 120) : Fin 4 → Fin 4 :=
  rhoIdx b g

/-- `rho` is multiplicative wherever both factors permute the blocks. -/
public theorem D28a_comp {b : Fin 4 → Bitset} {g h : Perm 120}
    (hg : ∀ a, ∃ c : Fin 4, imgSet g (b a) = b c)
    (hh : ∀ a, ∃ c : Fin 4, imgSet h (b a) = b c)
    (hinj : ∀ c d : Fin 4, b c = b d → c = d) (a : Fin 4) :
    D28a b (g.comp h) a = D28a b g (D28a b h a) := by
  refine hinj _ _ ?_
  have e1 : imgSet (g.comp h) (b a) = b (D28a b (g.comp h) a) :=
    rhoIdx_spec (by
      obtain ⟨c, hc⟩ := hh a
      obtain ⟨d, hd⟩ := hg c
      exact ⟨d, by rw [imgSet_comp, hc, hd]⟩)
  have e2 : imgSet h (b a) = b (D28a b h a) := rhoIdx_spec (hh a)
  have e3 : imgSet g (b (D28a b h a)) = b (D28a b g (D28a b h a)) :=
    rhoIdx_spec (hg _)
  rw [← e1, imgSet_comp, e2, e3]

/-- `D29`. `Ker := ker(rho)`: the gauge elements fixing every block. -/
@[expose] public def D29 (b : Fin 4 → Bitset) (g : Perm 120) : Prop :=
  D28 (union4 b) g ∧ ∀ a : Fin 4, D28a b g a = a

/-- On the kernel, `rho` being trivial is the same as fixing every block, which
is what makes `D29` the stabiliser `stabPres` of `D21a`. -/
public theorem rhoIdx_of_fixed {b : Fin 4 → Bitset} {g : Perm 120} {a : Fin 4}
    (hinj : ∀ c d : Fin 4, b c = b d → c = d) (hfix : imgSet g (b a) = b a) :
    rhoIdx b g a = a := by
  have hspec : imgSet g (b a) = b (rhoIdx b g a) := rhoIdx_spec ⟨a, hfix⟩
  rw [hfix] at hspec
  exact (hinj a (rhoIdx b g a) hspec).symm

/-- On the kernel, `rho` being trivial is the same as fixing every block, which
is what makes `D29` the stabiliser `stabPres` of `D21a`. The presentation must
be injective on indices for this to hold, and it is: an AtlasPresentation's
blocks are disjoint and nonempty, so no two indices carry the same block. -/
public theorem D29_iff_stabPres {b : Fin 4 → Bitset} {g : Perm 120}
    (hinj : ∀ c d : Fin 4, b c = b d → c = d)
    (h : ∀ a, ∃ c : Fin 4, imgSet g (b a) = b c) (hg : D21 g) :
    D29 b g ↔ stabPres b g := by
  constructor
  · rintro ⟨_, hk⟩
    refine ⟨hg, fun a => ?_⟩
    have e : imgSet g (b a) = b (D28a b g a) := rhoIdx_spec (h a)
    rw [hk a] at e
    exact e
  · intro hs
    exact ⟨stabPres_le_D28 hs, fun a => rhoIdx_of_fixed hinj (hs.2 a)⟩

/-! ## `D30`: the automorphism group of a single block -/

/-- The `Z`-span of the roots of a block: the integer combinations of roots
whose classes lie in `B`. `D30` quantifies over linear maps *of `span(B)`*, so
the span has to be a predicate before the maps can be. -/
public inductive SpanOf (B : Bitset) : Vec 8 Int → Prop where
  | root {x : Vec 8 Int} : RootsOf B x → SpanOf B x
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
    ∧ (∀ x : Vec 8 Int, RootsOf B x → RootsOf B (f x))
    ∧ ∃ g : Vec 8 Int → Vec 8 Int,
        (∀ x : Vec 8 Int, RootsOf B x → RootsOf B (g x))
          ∧ (∀ x : Vec 8 Int, RootsOf B x → g (f x) = x)
          ∧ (∀ x : Vec 8 Int, RootsOf B x → f (g x) = x)

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
  have hroot : ∀ x : Vec 8 Int, RootsOf B x → RootsOf B (AddCommGroup.neg x) := by
    rintro x ⟨hx, hc⟩
    exact ⟨D11_neg hx, by rw [D12_of_nrm (nrm_neg hx)]; exact hc⟩
  have hadd : ∀ x y : Vec 8 Int, (AddCommGroup.neg (fun i => x i + y i) : Vec 8 Int)
      = fun i => AddCommGroup.neg x i + AddCommGroup.neg y i :=
    fun x y => funext (fun i => by show -(x i + y i) = -(x i) + -(y i); omega)
  refine ⟨fun x y _ _ => hadd x y, fun x hx => SpanOf.neg hx, hroot,
    ⟨fun x => AddCommGroup.neg x, hroot, fun x _ => vneg_neg x, fun x _ => vneg_neg x⟩⟩

end UorAtlas.Gauge

end
