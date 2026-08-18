module
public import Init
public import UorAtlas.Prelude.Perm

/-!
Sections 7 and 9 of `UOR-ATLAS-FORMAL-001`: the categorical layer. `D23`
makes the AtlasInstances of `D22a` the objects of a category whose morphisms
are the elements of `Aut` that carry one instance to another, and sections 7
and 9 are the structural consequences: it is a connected groupoid (`T33`,
`T34`) whose hom-sets are right torsors under `Aut(W)` (`T40`, `T41`, `T42`),
so every hom-set has `|Aut(W)| = 4608` elements (`T35`), no object is initial
(`T36`), the isomorphism classes are a single class (`T37`), and the whole
category is equivalent to the one-object groupoid on `Aut(W)` (`T38`).
Dividing out the torsor action gives the thin category `D26`, in which every
hom-set is a singleton (`T44`, `D59`), every object is a zero object (`T45`),
and the skeleton is the one-object category whose object is the Atlas of `D27`
(`T46`).

## What this module is parameterised over, and why

`Aut` is `D21`'s subgroup of the permutations of the `120` classes and is
being built concurrently in `UorAtlas.Group`. This module therefore states
every theorem for an `ActionData`: a subgroup of `Perm n` given as a
*membership predicate* -- at `|Aut| = 348364800` no list of the group exists,
and `Perm.Gen` is exactly such a predicate -- acting on a type of objects, with
the population `IsOb` a single orbit of that action. Instantiating is supplying
that record: the group is `Perm.Gen` of `D21`'s generators, the objects are the
Bitsets of `UorAtlas.Blocks`, `IsOb` is `Atl`, and `transitive` is the document's
`T27`/`S24`, that `Atl` is one `Aut`-orbit. The two numbers the section states
enter through `AtlasAction.stab_card`, which is `T29`: `|Aut(W)| = 4608`.

Nothing here is a general category theory library. `Cat` is a record of exactly
the data `D23` gives -- objects, hom-types, identities, composition, three laws
-- because `D23`, `D26` and the skeleton of `T46` are three different categories
built from the same action, and `D24`, `T45` and `T46` each say which one they
are about.

## What is not here

`T47` and section 11's `T61` to `T64` are absent. A label is a claim about the
document and not merely about the mathematics, and the text of those five was
not available to this pass; a declaration named after a statement nobody read
would be indistinguishable from one that says something else, which is the
single failure this library exists to avoid. `T39p` and `T39` are likewise
absent, being the part of section 7 the group layer states.

## Counting without enumerating

`|Hom| = 4608` is `HasCard`: a duplicate-free list of the type, of that length.
The list is never computed -- it is transported along the torsor bijection from
the one `T29` supplies -- which is the whole reason the group layer's numbers
can be stated here without any object of size `348364800` ever being built.
-/

set_option autoImplicit false

namespace UorAtlas.Category

open UorAtlas.Prelude

/-! ## Cardinality

A type has `k` elements when some duplicate-free list of length `k` exhausts
it. Every count below is obtained from another count by a bijection, so this
is the only definition needed and `HasCard.ofBij` is the only way any of them
is proved. -/

/-- `alpha` has exactly `k` elements. -/
@[expose] public def HasCard (α : Type) (k : Nat) : Prop :=
  ∃ l : List α, l.Nodup ∧ (∀ a : α, a ∈ l) ∧ l.length = k

/-- Cardinality transports along a bijection: the enumeration is mapped across,
duplicate-free because the map has a left inverse and exhaustive because it has
a right inverse. -/
public theorem HasCard.ofBij {α β : Type} (f : α → β) (g : β → α)
    (hgf : ∀ a : α, g (f a) = a) (hfg : ∀ b : β, f (g b) = b) {k : Nat}
    (h : HasCard α k) : HasCard β k := by
  obtain ⟨l, hnd, hall, hlen⟩ := h
  refine ⟨l.map f, ?_, ?_, ?_⟩
  · exact List.Pairwise.map f (fun a b hab he => hab (by rw [← hgf a, he, hgf b])) hnd
  · exact fun b => List.mem_map.mpr ⟨g b, hall (g b), hfg b⟩
  · rw [List.length_map]; exact hlen

/-- A type with a single element has one element. -/
public theorem HasCard.one_of_unique {α : Type} (a : α) (h : ∀ b : α, b = a) : HasCard α 1 :=
  ⟨[a], by simp, fun b => by rw [h b]; exact List.mem_cons.mpr (Or.inl rfl), rfl⟩

/-- Two or more elements means two distinct elements. This is what refutes
initiality in `T36`: an initial object has exactly one morphism to each object,
and `4608` morphisms are more than one. -/
public theorem HasCard.exists_ne {α : Type} {k : Nat} (h : HasCard α k) (hk : 2 ≤ k) :
    ∃ a b : α, a ≠ b := by
  obtain ⟨l, hnd, _, hlen⟩ := h
  cases l with
  | nil => rw [List.length_nil] at hlen; omega
  | cons a t =>
    cases t with
    | nil => rw [List.length_cons, List.length_nil] at hlen; omega
    | cons b t' =>
      exact ⟨a, b, fun he =>
        (List.nodup_cons.mp hnd).1 (by rw [he]; exact List.mem_cons.mpr (Or.inl rfl))⟩

/-! ## Categories, initial and terminal objects

`Cat` is the record `D23` presents and nothing more; `D24` is initiality in
such a record. Terminality and the zero object are the same shape and are
needed by `T45` and `T46`. -/

/-- A category: objects, hom-types, identities, composition, and the three
laws. -/
public structure Cat where
  Ob : Type
  Hom : Ob → Ob → Type
  idm : (X : Ob) → Hom X X
  comp : {X Y Z : Ob} → Hom Y Z → Hom X Y → Hom X Z
  id_comp : ∀ {X Y : Ob} (f : Hom X Y), comp (idm Y) f = f
  comp_id : ∀ {X Y : Ob} (f : Hom X Y), comp f (idm X) = f
  assoc : ∀ {W X Y Z : Ob} (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
    comp (comp h g) f = comp h (comp g f)

/-- `D24`. `X` is **initial** in `C` when there is exactly one morphism from
`X` to each object. -/
@[expose] public def D24 (C : Cat) (X : C.Ob) : Prop :=
  ∀ Y : C.Ob, ∃ f : C.Hom X Y, ∀ g : C.Hom X Y, g = f

/-- `X` is **terminal** in `C` when there is exactly one morphism to `X` from
each object. -/
@[expose] public def IsTerminal (C : Cat) (X : C.Ob) : Prop :=
  ∀ Y : C.Ob, ∃ f : C.Hom Y X, ∀ g : C.Hom Y X, g = f

/-- A **zero object** is one that is both initial and terminal. -/
@[expose] public def IsZero (C : Cat) (X : C.Ob) : Prop := D24 C X ∧ IsTerminal C X

/-! ## The action the category is built from

A subgroup of `Perm n` as a membership predicate, acting on a type of objects,
together with the population that the section's category has as its objects and
the fact -- `T27` for `Atl` -- that the population is one orbit. -/

/-- The group-and-action data `D23` builds its category from. `Grp` is a
predicate rather than a list because `Aut` has `348364800` elements: `D21`
presents it by generators, `Perm.Gen` is that presentation, and no enumeration
of it is ever needed here. -/
public structure ActionData (n : Nat) where
  /-- The subgroup of `Perm n`; `Aut` of `D21`. -/
  Grp : Perm n → Prop
  one_mem : Grp (Perm.one n)
  comp_mem : ∀ {g h : Perm n}, Grp g → Grp h → Grp (g.comp h)
  inv_mem : ∀ {g : Perm n}, Grp g → Grp g.inv
  /-- The type the group acts on; the Bitsets of `D22a` in the instantiation. -/
  Obj : Type
  act : Perm n → Obj → Obj
  act_one : ∀ W : Obj, act (Perm.one n) W = W
  act_comp : ∀ (g h : Perm n) (W : Obj), act (g.comp h) W = act g (act h W)
  /-- The population; `Atl` of `D22` in the instantiation. -/
  IsOb : Obj → Prop
  stable : ∀ {g : Perm n}, Grp g → ∀ {W : Obj}, IsOb W → IsOb (act g W)
  base : Obj
  base_isOb : IsOb base
  /-- The population is a single orbit: `T27` for `Atl`. -/
  transitive : ∀ {W : Obj}, IsOb W → ∃ g : Perm n, Grp g ∧ act g base = W

namespace Atl

variable {n : Nat}

/-- The objects of `D23`: the members of the population. -/
public abbrev Ob (A : ActionData n) : Type := { W : A.Obj // A.IsOb W }

/-- The morphisms of `D23`: the group elements carrying `X` to `Y`. -/
public abbrev Hom (A : ActionData n) (X Y : Ob A) : Type :=
  { g : Perm n // A.Grp g ∧ A.act g X.val = Y.val }

/-- The distinguished object; `W` in the document's statements. -/
@[expose] public def basePt (A : ActionData n) : Ob A := ⟨A.base, A.base_isOb⟩

/-- The identity morphism: the identity of the group. -/
@[expose] public def idHom (A : ActionData n) (X : Ob A) : Hom A X X :=
  ⟨Perm.one n, A.one_mem, A.act_one X.val⟩

/-- Composition of morphisms: the product in the group, in the same order. -/
@[expose] public def compHom {A : ActionData n} {X Y Z : Ob A}
    (f : Hom A Y Z) (g : Hom A X Y) : Hom A X Z :=
  ⟨f.val.comp g.val, A.comp_mem f.property.1 g.property.1, by
    rw [A.act_comp, g.property.2, f.property.2]⟩

/-- The inverse morphism. It is a morphism `Y -> X` because the action is by a
group: `g` carries `X` to `Y`, so `g.inv` carries `Y` back. -/
@[expose] public def invHom {A : ActionData n} {X Y : Ob A} (f : Hom A X Y) : Hom A Y X :=
  ⟨f.val.inv, A.inv_mem f.property.1, by
    -- Rewriting `X -> Y` backwards inside the goal is not type correct, because
    -- `f`'s own type mentions `Y.val`; the identity is therefore built forwards
    -- and the image of `X` replaced afterwards.
    have h : A.act f.val.inv (A.act f.val X.val) = X.val := by
      rw [← A.act_comp, Perm.inv_comp]
      exact A.act_one X.val
    rw [f.property.2] at h
    exact h⟩

end Atl

/-! ## `D23`: the category `Atl` -/

open Atl

/-- `D23`. The category whose objects are the AtlasInstances and whose
morphisms `W -> W'` are the elements of `Aut` carrying `W` to `W'`. The three
laws are the group laws of `Perm`, which hold on the nose. -/
@[expose] public def D23 {n : Nat} (A : ActionData n) : Cat where
  Ob := Atl.Ob A
  Hom := Atl.Hom A
  idm := Atl.idHom A
  comp := Atl.compHom
  id_comp f := Subtype.ext (Perm.one_comp f.val)
  comp_id f := Subtype.ext (Perm.comp_one f.val)
  assoc h g f := Subtype.ext (Perm.comp_assoc h.val g.val f.val)

/-! ## `T33` and `T34`: a connected groupoid -/

/-- `T33`. `Atl` is a **groupoid**: every morphism has a two-sided inverse. -/
public theorem T33 {n : Nat} (A : ActionData n) (X Y : Atl.Ob A) (f : Atl.Hom A X Y) :
    ∃ g : Atl.Hom A Y X, compHom g f = idHom A X ∧ compHom f g = idHom A Y :=
  ⟨invHom f, Subtype.ext (Perm.inv_comp f.val), Subtype.ext (Perm.comp_inv f.val)⟩

/-- Every object is reached from the base object, which is `transitive` read as
a morphism. -/
public theorem homFromBase {n : Nat} (A : ActionData n) (X : Atl.Ob A) :
    Nonempty (Atl.Hom A (basePt A) X) := by
  obtain ⟨g, hg, hgb⟩ := A.transitive X.property
  exact ⟨⟨g, hg, hgb⟩⟩

/-- `T34`. `Atl` is **connected**: there is a morphism between any two objects,
and by `T33` it is an isomorphism. -/
public theorem T34 {n : Nat} (A : ActionData n) (X Y : Atl.Ob A) :
    Nonempty (Atl.Hom A X Y) := by
  exact (homFromBase A X).elim fun f => (homFromBase A Y).elim fun g => ⟨compHom g (invHom f)⟩

/-! ## `D25`: the automorphism group of an object -/

/-- `D25`. `Aut(W)`, the automorphisms of one object: the stabiliser of `W` in
`Aut`. -/
public abbrev D25 {n : Nat} (A : ActionData n) (X : Atl.Ob A) : Type := Atl.Hom A X X

namespace D25

variable {n : Nat} {A : ActionData n} {X : Atl.Ob A}

@[expose] public def one (A : ActionData n) (X : Atl.Ob A) : D25 A X := idHom A X

@[expose] public def mul (a b : D25 A X) : D25 A X := compHom a b

@[expose] public def inv (a : D25 A X) : D25 A X := invHom a

public theorem one_mul (a : D25 A X) : mul (one A X) a = a := Subtype.ext (Perm.one_comp a.val)

public theorem mul_one (a : D25 A X) : mul a (one A X) = a := Subtype.ext (Perm.comp_one a.val)

public theorem mul_assoc (a b c : D25 A X) : mul (mul a b) c = mul a (mul b c) :=
  Subtype.ext (Perm.comp_assoc a.val b.val c.val)

public theorem inv_mul (a : D25 A X) : mul (inv a) a = one A X :=
  Subtype.ext (Perm.inv_comp a.val)

public theorem mul_inv (a : D25 A X) : mul a (inv a) = one A X :=
  Subtype.ext (Perm.comp_inv a.val)

end D25

/-! ## `T40`, `T41`, `T42`: the hom-sets are right torsors

`Hom(W,W')` carries a right action of `Aut(W)` by precomposition. `T42` is that
the action is free and transitive on a nonempty set, which is what makes
`Hom(W,W')` a right `Aut(W)`-torsor, and `T41` reads the cardinality off that:
choosing any one morphism identifies the hom-set with the group. -/

/-- The right action of `Aut(W)` on `Hom(W,W')`: precomposition. -/
@[expose] public def rAct {n : Nat} {A : ActionData n} {X Y : Atl.Ob A}
    (f : Atl.Hom A X Y) (a : D25 A X) : Atl.Hom A X Y := compHom f a

/-- `T40`. Precomposition is a right action of `Aut(W)` on `Hom(W,W')`. -/
public theorem T40 {n : Nat} (A : ActionData n) (X Y : Atl.Ob A) :
    (∀ f : Atl.Hom A X Y, rAct f (D25.one A X) = f)
      ∧ (∀ (f : Atl.Hom A X Y) (a b : D25 A X),
          rAct (rAct f a) b = rAct f (D25.mul a b)) :=
  ⟨fun f => Subtype.ext (Perm.comp_one f.val),
   fun f a b => Subtype.ext (Perm.comp_assoc f.val a.val b.val)⟩

/-- `T42`. `Hom(W,W')` is a **right torsor** under `Aut(W)`: it is nonempty,
and the action of `T40` is free and transitive. -/
public theorem T42 {n : Nat} (A : ActionData n) (X Y : Atl.Ob A) :
    Nonempty (Atl.Hom A X Y)
      ∧ (∀ (f : Atl.Hom A X Y) (a b : D25 A X), rAct f a = rAct f b → a = b)
      ∧ (∀ f f' : Atl.Hom A X Y, ∃ a : D25 A X, rAct f a = f') := by
  refine ⟨T34 A X Y, ?_, ?_⟩
  · intro f a b hab
    exact Subtype.ext (Perm.comp_left_cancel (congrArg Subtype.val hab))
  · intro f f'
    refine ⟨compHom (invHom f) f', Subtype.ext ?_⟩
    show f.val.comp (f.val.inv.comp f'.val) = f'.val
    rw [← Perm.comp_assoc, Perm.comp_inv, Perm.one_comp]

/-- Choosing one morphism `X -> Y` identifies `Aut(X)` with `Hom(X,Y)`, so the
two have the same cardinality. This is the counting content of `T42`. -/
public theorem card_hom_of_card_aut {n : Nat} {A : ActionData n} {X Y : Atl.Ob A}
    (f₀ : Atl.Hom A X Y) {k : Nat} (h : HasCard (D25 A X) k) : HasCard (Atl.Hom A X Y) k := by
  refine HasCard.ofBij (fun a => compHom f₀ a) (fun b => compHom (invHom f₀) b) ?_ ?_ h
  · intro a
    refine Subtype.ext ?_
    show f₀.val.inv.comp (f₀.val.comp a.val) = a.val
    rw [← Perm.comp_assoc, Perm.inv_comp, Perm.one_comp]
  · intro b
    refine Subtype.ext ?_
    show f₀.val.comp (f₀.val.inv.comp b.val) = b.val
    rw [← Perm.comp_assoc, Perm.comp_inv, Perm.one_comp]

/-- All the automorphism groups are conjugate, so they all have the size the
group layer computes at the base object. -/
public theorem card_aut_of_card_base {n : Nat} {A : ActionData n} (X : Atl.Ob A) {k : Nat}
    (h : HasCard (D25 A (basePt A)) k) : HasCard (D25 A X) k := by
  refine (homFromBase A X).elim (fun f => ?_)
  refine HasCard.ofBij (fun a => compHom f (compHom a (invHom f)))
    (fun b => compHom (invHom f) (compHom b f)) ?_ ?_ h
  · intro a
    refine Subtype.ext ?_
    show f.val.inv.comp ((f.val.comp (a.val.comp f.val.inv)).comp f.val) = a.val
    rw [Perm.comp_assoc, Perm.comp_assoc, Perm.inv_comp, Perm.comp_one,
      ← Perm.comp_assoc, Perm.inv_comp, Perm.one_comp]
  · intro b
    refine Subtype.ext ?_
    show f.val.comp ((f.val.inv.comp (b.val.comp f.val)).comp f.val.inv) = b.val
    rw [Perm.comp_assoc, Perm.comp_assoc, Perm.comp_inv, Perm.comp_one,
      ← Perm.comp_assoc, Perm.comp_inv, Perm.one_comp]

/-! ## `T43`: the orbit map `Aut / Aut(W) -> Ob(Atl)`

The cosets of `Aut(W)` in `Aut` are the fibres of `g |-> g . W`, which is the
content of `T43` and, with `T29`, the route the document takes to `T28`. The
quotient is by the right-coset relation, so injectivity is a genuine step: two
group elements with the same image differ by a stabiliser element. -/

/-- An element of the group. -/
public abbrev GrpEl {n : Nat} (A : ActionData n) : Type := { g : Perm n // A.Grp g }

/-- The right cosets of `Aut(W)`: `h` lies in `g . Aut(W)`. -/
@[expose] public def CosetRel {n : Nat} (A : ActionData n) (g h : GrpEl A) : Prop :=
  ∃ a : Perm n, A.Grp a ∧ A.act a A.base = A.base ∧ h.val = g.val.comp a

/-- `Aut / Aut(W)`. -/
public abbrev Cosets {n : Nat} (A : ActionData n) : Type := Quot (CosetRel A)

/-- The coset relation is an equivalence, so the quotient by it is the coset
space `Aut / Aut(W)` itself and not some coarser identification -- without
which `T43`'s injectivity would be a claim about the wrong quotient. -/
public theorem cosetRel_equivalence {n : Nat} (A : ActionData n) :
    (∀ g : GrpEl A, CosetRel A g g)
      ∧ (∀ g h : GrpEl A, CosetRel A g h → CosetRel A h g)
      ∧ (∀ g h k : GrpEl A, CosetRel A g h → CosetRel A h k → CosetRel A g k) := by
  refine ⟨fun g => ⟨Perm.one n, A.one_mem, A.act_one A.base, (Perm.comp_one g.val).symm⟩, ?_, ?_⟩
  · rintro g h ⟨a, ha, hab, hh⟩
    refine ⟨a.inv, A.inv_mem ha, ?_, ?_⟩
    · have h1 : A.act a.inv (A.act a A.base) = A.base := by
        rw [← A.act_comp, Perm.inv_comp]
        exact A.act_one A.base
      rw [hab] at h1
      exact h1
    · rw [hh, Perm.comp_assoc, Perm.comp_inv, Perm.comp_one]
  · rintro g h k ⟨a, ha, hab, hh⟩ ⟨b, hb, hbb, hk⟩
    refine ⟨a.comp b, A.comp_mem ha hb, ?_, ?_⟩
    · rw [A.act_comp, hbb, hab]
    · rw [hk, hh, Perm.comp_assoc]

/-- The orbit map `Aut / Aut(W) -> Ob(Atl)`, `g . Aut(W) |-> g . W`. -/
@[expose] public def orbitMap {n : Nat} (A : ActionData n) : Cosets A → Atl.Ob A :=
  Quot.lift (fun g => (⟨A.act g.val A.base, A.stable g.property A.base_isOb⟩ : Atl.Ob A))
    (by
      intro g h hgh
      obtain ⟨a, _, hab, hh⟩ := hgh
      refine Subtype.ext ?_
      show A.act g.val A.base = A.act h.val A.base
      rw [hh, A.act_comp, hab])

public theorem orbitMap_mk {n : Nat} (A : ActionData n) (g : GrpEl A) :
    (orbitMap A (Quot.mk (CosetRel A) g)).val = A.act g.val A.base := rfl

/-- `T43`. The orbit map is a **bijection**: injective because two elements
with the same image differ by a stabiliser element, surjective because the
population is one orbit. -/
public theorem T43 {n : Nat} (A : ActionData n) :
    (∀ p q : Cosets A, orbitMap A p = orbitMap A q → p = q)
      ∧ (∀ X : Atl.Ob A, ∃ p : Cosets A, orbitMap A p = X) := by
  refine ⟨?_, ?_⟩
  · refine Quot.ind (β := fun p => ∀ q, orbitMap A p = orbitMap A q → p = q) ?_
    intro g
    refine Quot.ind
      (β := fun q => orbitMap A (Quot.mk (CosetRel A) g) = orbitMap A q →
        Quot.mk (CosetRel A) g = q) ?_
    intro h hgh
    have hv : A.act g.val A.base = A.act h.val A.base := congrArg Subtype.val hgh
    refine Quot.sound ⟨g.val.inv.comp h.val,
      A.comp_mem (A.inv_mem g.property) h.property, ?_, ?_⟩
    · rw [A.act_comp, ← hv, ← A.act_comp, Perm.inv_comp]
      exact A.act_one A.base
    · show h.val = g.val.comp (g.val.inv.comp h.val)
      rw [← Perm.comp_assoc, Perm.comp_inv, Perm.one_comp]
  · intro X
    obtain ⟨g, hg, hgb⟩ := A.transitive X.property
    exact ⟨Quot.mk (CosetRel A) ⟨g, hg⟩, Subtype.ext hgb⟩

/-! ## `T35`, `T36`, `T41`: the size of a hom-set

`AtlasAction` is `ActionData` together with the one number the group layer
computes: `T29`'s `|Aut(W)| = 4608`. Everything in this section is that number
transported along the torsor bijection of `T42`. -/

/-- The action of `D23` with the stabiliser order `T29` establishes. -/
public structure AtlasAction (n : Nat) extends ActionData n where
  /-- `T29`: `|Aut(W)| = |Gauge(W)| = 4608`. -/
  stab_card : HasCard (D25 toActionData (basePt toActionData)) 4608

/-- `T35`. Every hom-set of `Atl` has `4608` elements. -/
public theorem T35 {n : Nat} (A : AtlasAction n) (X Y : Atl.Ob A.toActionData) :
    HasCard (Atl.Hom A.toActionData X Y) 4608 :=
  (T34 A.toActionData X Y).elim fun f =>
    card_hom_of_card_aut f (card_aut_of_card_base X A.stab_card)

/-- `T41`. `|Hom(W,W')| = |Aut(W)| = 4608`: the torsor of `T42` has the
cardinality of the group acting on it. -/
public theorem T41 {n : Nat} (A : AtlasAction n) (X Y : Atl.Ob A.toActionData) :
    HasCard (D25 A.toActionData X) 4608 ∧ HasCard (Atl.Hom A.toActionData X Y) 4608 :=
  ⟨card_aut_of_card_base X A.stab_card, T35 A X Y⟩

/-- `T36`. **No object of `Atl` is initial.** An initial object has exactly one
endomorphism; every object of `Atl` has `4608` of them. -/
public theorem T36 {n : Nat} (A : AtlasAction n) (X : Atl.Ob A.toActionData) :
    ¬ D24 (D23 A.toActionData) X := by
  intro hinit
  obtain ⟨f, g, hfg⟩ := (T35 A X X).exists_ne (by decide)
  obtain ⟨t, ht⟩ := hinit X
  exact hfg ((ht f).trans (ht g).symm)

/-! ## `T37`: the isomorphism classes

By `T33` every morphism is an isomorphism, so `Isoc` -- being connected by a
morphism -- is the isomorphism relation, and by `T34` it is total. -/

/-- Isomorphism of objects: in a groupoid, connectedness by a morphism. -/
@[expose] public def Isoc {n : Nat} (A : ActionData n) (X Y : Atl.Ob A) : Prop :=
  Nonempty (Atl.Hom A X Y)

/-- The objects of the skeleton: the isomorphism classes. -/
public abbrev SkelOb {n : Nat} (A : ActionData n) : Type := Quot (Isoc A)

/-- There is only one isomorphism class, and the base object represents it.
Everything the skeleton needs follows from this one statement. -/
public theorem skel_unique {n : Nat} (A : ActionData n) (p : SkelOb A) :
    p = Quot.mk (Isoc A) (basePt A) :=
  Quot.ind (β := fun p => p = Quot.mk (Isoc A) (basePt A))
    (fun a => Quot.sound (T34 A a (basePt A))) p

/-- `T37`. The skeleton of `Atl` has exactly **one object**. -/
public theorem T37 {n : Nat} (A : ActionData n) : HasCard (SkelOb A) 1 :=
  HasCard.one_of_unique (Quot.mk (Isoc A) (basePt A)) (skel_unique A)

/-! ## `T38`: `Atl` is equivalent to a one-object groupoid of order 4608 -/

/-- A functor between two of these categories. -/
public structure CatFunctor (C D : Cat) where
  obj : C.Ob → D.Ob
  map : {X Y : C.Ob} → C.Hom X Y → D.Hom (obj X) (obj Y)
  map_id : ∀ X : C.Ob, map (C.idm X) = D.idm (obj X)
  map_comp : ∀ {X Y Z : C.Ob} (f : C.Hom Y Z) (g : C.Hom X Y),
    map (C.comp f g) = D.comp (map f) (map g)

/-- A functor is an **equivalence** when it is faithful, full and essentially
surjective. Essential surjectivity is stated as connectedness by a morphism,
which in a groupoid is isomorphism (`T33`). -/
@[expose] public def IsCatEquivalence {C D : Cat} (F : CatFunctor C D) : Prop :=
  (∀ (X Y : C.Ob) (f g : C.Hom X Y), F.map f = F.map g → f = g)
    ∧ (∀ (X Y : C.Ob) (h : D.Hom (F.obj X) (F.obj Y)), ∃ f : C.Hom X Y, F.map f = h)
    ∧ (∀ Z : D.Ob, ∃ X : C.Ob, Nonempty (D.Hom (F.obj X) Z))

/-- The one-object groupoid on `Aut(W)`: one object, and `Aut(W)` as its
endomorphisms. -/
@[expose] public def autGroupoid {n : Nat} (A : ActionData n) : Cat where
  Ob := Unit
  Hom _ _ := D25 A (basePt A)
  idm _ := D25.one A (basePt A)
  comp f g := D25.mul f g
  id_comp f := D25.one_mul f
  comp_id f := D25.mul_one f
  assoc h g f := D25.mul_assoc h g f

/-- The functor sending the one object to `W` and each automorphism to itself. -/
@[expose] public def deloopFunctor {n : Nat} (A : ActionData n) :
    CatFunctor (autGroupoid A) (D23 A) where
  obj _ := basePt A
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `T38`. `Atl` is **equivalent** to a one-object groupoid whose morphisms are
`4608` in number. -/
public theorem T38 {n : Nat} (A : AtlasAction n) :
    IsCatEquivalence (deloopFunctor A.toActionData)
      ∧ HasCard (autGroupoid A.toActionData).Ob 1
      ∧ HasCard ((autGroupoid A.toActionData).Hom () ()) 4608
      ∧ ∀ f : (autGroupoid A.toActionData).Hom () (),
          ∃ g : (autGroupoid A.toActionData).Hom () (),
            (autGroupoid A.toActionData).comp g f = (autGroupoid A.toActionData).idm ()
              ∧ (autGroupoid A.toActionData).comp f g = (autGroupoid A.toActionData).idm () := by
  refine ⟨⟨fun _ _ _ _ h => h, fun _ _ h => ⟨h, rfl⟩, fun Z => ⟨(), homFromBase _ Z⟩⟩,
    HasCard.one_of_unique () (fun _ => rfl), A.stab_card, fun f => ?_⟩
  exact ⟨D25.inv f, D25.inv_mul f, D25.mul_inv f⟩

/-! ## `D26`, `D59`, `T44`, `T45`: the thin category `Atl // Aut`

Dividing each hom-set by the right action of `T40` collapses the `4608`
morphisms `W -> W'` to one, because the action is transitive (`T42`). The
quotient composes because any two of its morphisms with the same source and
target are equal, which is also why every object of it is a zero object. -/

/-- The identification `D26` makes: two morphisms `W -> W'` are the same thin
morphism when they differ by an automorphism of `W`, so the thin morphisms are
the orbits of `T40`'s right action. -/
@[expose] public def ThinRel {n : Nat} (A : ActionData n) (X Y : Atl.Ob A)
    (f g : Atl.Hom A X Y) : Prop := ∃ a : D25 A X, rAct f a = g

/-- The hom-sets of `Thin(Atl)`. -/
public abbrev ThinHom {n : Nat} (A : ActionData n) (X Y : Atl.Ob A) : Type :=
  Quot (ThinRel A X Y)

/-- Any two thin morphisms with the same source and target are equal: `T42`'s
transitivity, read in the quotient. -/
public theorem thin_unique {n : Nat} (A : ActionData n) (X Y : Atl.Ob A)
    (p q : ThinHom A X Y) : p = q := by
  refine Quot.ind (β := fun p => ∀ q, p = q) ?_ p q
  intro f
  refine Quot.ind (β := fun q => Quot.mk (ThinRel A X Y) f = q) ?_
  intro g
  exact Quot.sound ((T42 A X Y).2.2 f g)

/-- Composition descends to the quotient. The lifts' side conditions are
`thin_unique`: any two candidates for the value are already equal. -/
@[expose] public def thinComp {n : Nat} {A : ActionData n} {X Y Z : Atl.Ob A}
    (f : ThinHom A Y Z) (g : ThinHom A X Y) : ThinHom A X Z :=
  Quot.lift
    (fun f0 => Quot.lift (fun g0 => Quot.mk (ThinRel A X Z) (compHom f0 g0))
      (fun _ _ _ => thin_unique A X Z _ _) g)
    (fun _ _ _ => thin_unique A X Z _ _) f

/-- `D26`. **`Thin(Atl)`**: the same objects as `Atl`, with each hom-set
divided by the right `Aut(W)`-action. -/
@[expose] public def D26 {n : Nat} (A : ActionData n) : Cat where
  Ob := Atl.Ob A
  Hom := ThinHom A
  idm X := Quot.mk (ThinRel A X X) (idHom A X)
  comp f g := thinComp f g
  id_comp _ := thin_unique A _ _ _ _
  comp_id _ := thin_unique A _ _ _ _
  assoc _ _ _ := thin_unique A _ _ _ _

/-- `D59`. The sizes of the hom-sets of `Thin(Atl)`, one entry per ordered pair
of objects. `D59_spec` is that this table is correct. -/
@[expose] public def D59 {n : Nat} (A : ActionData n) : Atl.Ob A → Atl.Ob A → Nat :=
  fun _ _ => 1

/-- `T44`. `|Hom'(W,W')| = 1`: the quotient of a hom-set by the free transitive
action of `T42` is a single point. -/
public theorem T44 {n : Nat} (A : ActionData n) (X Y : Atl.Ob A) :
    HasCard (ThinHom A X Y) 1 :=
  (T34 A X Y).elim fun f =>
    HasCard.one_of_unique (Quot.mk (ThinRel A X Y) f) (fun q => thin_unique A X Y q _)

/-- `D59`'s table is correct: it is `T44` read as a size per ordered pair. -/
public theorem D59_spec {n : Nat} (A : ActionData n) (X Y : Atl.Ob A) :
    HasCard (ThinHom A X Y) (D59 A X Y) := T44 A X Y

/-- `T45`. In `Atl // Aut` **every object is both initial and terminal**. -/
public theorem T45 {n : Nat} (A : ActionData n) (X : Atl.Ob A) : IsZero (D26 A) X := by
  refine ⟨fun Y => ?_, fun Y => ?_⟩
  · exact (T34 A X Y).elim fun f =>
      ⟨Quot.mk (ThinRel A X Y) f, fun g => thin_unique A X Y g _⟩
  · exact (T34 A Y X).elim fun f =>
      ⟨Quot.mk (ThinRel A Y X) f, fun g => thin_unique A Y X g _⟩

/-! ## `D27`, `T46`: the Atlas is a zero object of the skeleton

`T37` says there is one isomorphism class, so a representative of a class can
be chosen without any appeal to choice: the base object represents the only
class there is. The skeleton of `Thin(Atl)` is therefore the full subcategory
on that representative, and its single object is the Atlas. -/

/-- The representative of an isomorphism class. Constant because `T37` says
there is only one class to represent. -/
@[expose] public def skelRep {n : Nat} (A : ActionData n) : SkelOb A → Atl.Ob A :=
  fun _ => basePt A

/-- The chosen representative really represents its class. -/
public theorem skelRep_section {n : Nat} (A : ActionData n) (p : SkelOb A) :
    Quot.mk (Isoc A) (skelRep A p) = p := (skel_unique A p).symm

/-- `skel(Thin(Atl))`: the isomorphism classes, with the thin morphisms between
their representatives. -/
@[expose] public def skelThin {n : Nat} (A : ActionData n) : Cat where
  Ob := SkelOb A
  Hom p q := ThinHom A (skelRep A p) (skelRep A q)
  idm p := Quot.mk (ThinRel A (skelRep A p) (skelRep A p)) (idHom A (skelRep A p))
  comp f g := thinComp f g
  id_comp _ := thin_unique A _ _ _ _
  comp_id _ := thin_unique A _ _ _ _
  assoc _ _ _ := thin_unique A _ _ _ _

/-- `D27`. The **Atlas**: the single isomorphism class of AtlasInstances, the
one object of `skel(Thin(Atl))`. -/
@[expose] public def D27 {n : Nat} (A : ActionData n) : SkelOb A :=
  Quot.mk (Isoc A) (basePt A)

/-- `T46`. The Atlas is a **zero object** of `skel(Thin(Atl))`. -/
public theorem T46 {n : Nat} (A : ActionData n) : IsZero (skelThin A) (D27 A) := by
  refine ⟨fun q => ?_, fun q => ?_⟩
  · exact (T34 A (skelRep A (D27 A)) (skelRep A q)).elim fun f =>
      ⟨Quot.mk (ThinRel A (skelRep A (D27 A)) (skelRep A q)) f,
        fun g => thin_unique A (skelRep A (D27 A)) (skelRep A q) g _⟩
  · exact (T34 A (skelRep A q) (skelRep A (D27 A))).elim fun f =>
      ⟨Quot.mk (ThinRel A (skelRep A q) (skelRep A (D27 A))) f,
        fun g => thin_unique A (skelRep A q) (skelRep A (D27 A)) g _⟩

/-! ## The framework is inhabited

Every theorem above is stated for an `ActionData`, so a reader is owed a
witness that the record can be built and that the counting hypothesis is
satisfiable -- otherwise `T35` and `T41` would be true of nothing. `Sym(3)`
acting on its three points is the smallest action of the shape `D23` needs: a
group presented by generators exactly as `D21` presents `Aut`, one orbit, and a
stabiliser larger than the identity. At that size the stabiliser has `2`
elements rather than `4608`, and the hom-set count is proved by the same
`card_hom_of_card_aut` that `T35` uses -- so what the group layer will supply
for `Aut` is one number, not one argument. -/

namespace SymThree

open UorAtlas.Prelude.Perm

/-- `Sym(3)` acting on the three points it permutes. -/
@[expose] public def action : ActionData 3 where
  Grp := Gen symThreeGens
  one_mem := Gen.one
  comp_mem := Gen.comp_mem
  inv_mem := Gen.inv_mem
  Obj := Fin 3
  act g W := g.toFun W
  act_one _ := rfl
  act_comp _ _ _ := rfl
  IsOb _ := True
  stable := by intro _ _ _ _; exact trivial
  base := 0
  base_isOb := trivial
  transitive := by
    intro W _
    have h : ∀ W : Fin 3, ∃ g ∈ symThreeList, g.toFun 0 = W := by decide +kernel
    obtain ⟨g, hg, hgW⟩ := h W
    exact ⟨g, ((closure_spec symThree_closure).2.2 g).mp hg, hgW⟩

/-- The non-identity permutation fixing `0`, built from the generators by
conjugation rather than transcribed: `cycleThree` carries `0,1` to `1,2`, so it
carries the transposition of `0,1` to the transposition of `1,2`. -/
@[expose] public def fixZero : Perm 3 := cycleThree.comp (swapThree.comp cycleThree.inv)

public theorem fixZero_gen : Gen symThreeGens fixZero :=
  ((closure_spec symThree_closure).2.2 fixZero).mp (by decide +kernel)

/-- The stabiliser of the base point has two elements. This is the example's
analogue of `T29`, and it is what `AtlasAction.stab_card` will carry for
`Aut`. -/
public theorem stab_card : HasCard (D25 action (basePt action)) 2 := by
  refine ⟨[idHom action (basePt action), ⟨fixZero, fixZero_gen, by show fixZero.toFun (0 : Fin 3) = (0 : Fin 3); decide +kernel⟩],
    ?_, ?_, rfl⟩
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
    intro hm
    have hv : (idHom action (basePt action)).val = fixZero :=
      congrArg Subtype.val (List.mem_singleton.mp hm)
    exact absurd hv (by decide)
  · intro a
    have hmem : a.val ∈ symThreeList :=
      ((closure_spec symThree_closure).2.2 a.val).mpr a.property.1
    have hcase : ∀ g ∈ symThreeList, g.toFun 0 = 0 → g = Perm.one 3 ∨ g = fixZero := by
      decide +kernel
    rcases hcase a.val hmem a.property.2 with h | h
    · exact List.mem_cons.mpr (Or.inl (Subtype.ext h))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl (Subtype.ext h))))

/-- The hom-set count of `T35` at this size, by the same proof: every hom-set
has as many elements as the stabiliser. -/
public theorem hom_card (X Y : Atl.Ob action) : HasCard (Atl.Hom action X Y) 2 :=
  (T34 action X Y).elim fun f => card_hom_of_card_aut f (card_aut_of_card_base X stab_card)

/-- No object is initial here either, for the reason `T36` gives: `2` is not
`1`. -/
public theorem not_initial (X : Atl.Ob action) : ¬ D24 (D23 action) X := by
  intro hinit
  obtain ⟨f, g, hfg⟩ := (hom_card X X).exists_ne (by decide)
  obtain ⟨t, ht⟩ := hinit X
  exact hfg ((ht f).trans (ht g).symm)

end SymThree

end UorAtlas.Category
