module

public import Init
public import UorAtlas.ClosureGauge

set_option autoImplicit false
set_option maxRecDepth 40000

public section

namespace UorAtlas.Closure

open UorAtlas.Prelude
open UorAtlas.Prelude.ListAux
open UorAtlas.Prelude.Linear
open UorAtlas.Roots
open UorAtlas.Blocks
open UorAtlas.Group
open UorAtlas.Census

/-! ## Presentations of an AtlasInstance -/

public theorem disjoint_of_union_disjoint {A B C D : Bitset}
    (h : Bitset.inter (Bitset.union A B) (Bitset.union C D) = Bitset.empty) :
    (Bitset.inter A C = Bitset.empty ∧ Bitset.inter A D = Bitset.empty)
      ∧ (Bitset.inter B C = Bitset.empty ∧ Bitset.inter B D = Bitset.empty) := by
  have one : ∀ S T, (S = A ∨ S = B) → (T = C ∨ T = D) →
      Bitset.inter S T = Bitset.empty := by
    intro S T hS hT
    refine Bitset.ext (fun i => ⟨fun hm => ?_, fun hm => absurd hm (Bitset.notMem_empty i)⟩)
    have hm' := (Bitset.mem_inter S T i).mp hm
    have hU : i ∈ Bitset.inter (Bitset.union A B) (Bitset.union C D) := by
      apply (Bitset.mem_inter _ _ i).mpr
      refine ⟨(Bitset.mem_union A B i).mpr ?_, (Bitset.mem_union C D i).mpr ?_⟩
      · rcases hS with rfl | rfl
        · exact Or.inl hm'.1
        · exact Or.inr hm'.1
      · rcases hT with rfl | rfl
        · exact Or.inl hm'.2
        · exact Or.inr hm'.2
    rw [h] at hU
    exact absurd hU (Bitset.notMem_empty i)
  exact ⟨⟨one A C (Or.inl rfl) (Or.inl rfl), one A D (Or.inl rfl) (Or.inr rfl)⟩,
    ⟨one B C (Or.inr rfl) (Or.inl rfl), one B D (Or.inr rfl) (Or.inr rfl)⟩⟩

public theorem inter_empty_comm {A B : Bitset}
    (h : Bitset.inter A B = Bitset.empty) :
    Bitset.inter B A = Bitset.empty := by
  refine Bitset.ext (fun i => ?_)
  constructor
  · intro hm
    have hm' : i ∈ Bitset.inter A B :=
      (Bitset.mem_inter A B i).mpr ((Bitset.mem_inter B A i).mp hm).symm
    rw [h] at hm'
    exact False.elim (absurd hm' (Bitset.notMem_empty i))
  · intro hm
    exact False.elim (absurd hm (Bitset.notMem_empty i))

public theorem presentation_of_atl {W : Bitset} (hW : Atl W) :
    ∃ A : D17, V A = W := by
  obtain ⟨B0, B1, B2, B3, hF, hG, hd, hV, ht⟩ := hW
  let b : Fin 4 → Bitset := fun a =>
    if a = 0 then B0 else if a = 1 then B1 else if a = 2 then B2 else B3
  have hb : b 0 = B0 ∧ b 1 = B1 ∧ b 2 = B2 ∧ b 3 = B3 := by
    simp [b]
  have hcross := disjoint_of_union_disjoint hd
  have his : ∀ a : Fin 4, Blk (b a) := by
    intro a
    refine fin4 (P := fun a => Blk (b a)) ?_ ?_ ?_ ?_ a
    · rw [hb.1]; exact hF.1
    · rw [hb.2.1]; exact hF.2.1
    · rw [hb.2.2.1]; exact hG.1
    · rw [hb.2.2.2]; exact hG.2.1
  have hdis : ∀ a c : Fin 4, a ≠ c → Bitset.inter (b a) (b c) = Bitset.empty := by
    intro a
    refine fin4 (P := fun a => ∀ c, a ≠ c → Bitset.inter (b a) (b c) = Bitset.empty)
      ?_ ?_ ?_ ?_ a
    all_goals intro c
    · refine fin4 (P := fun c => (0 : Fin 4) ≠ c →
          Bitset.inter (b 0) (b c) = Bitset.empty) ?_ ?_ ?_ ?_ c
      · intro h; exact absurd rfl h
      · intro _; rw [hb.1, hb.2.1]; exact hF.2.2.1
      · intro _; rw [hb.1, hb.2.2.1]; exact hcross.1.1
      · intro _; rw [hb.1, hb.2.2.2]; exact hcross.1.2
    · refine fin4 (P := fun c => (1 : Fin 4) ≠ c →
          Bitset.inter (b 1) (b c) = Bitset.empty) ?_ ?_ ?_ ?_ c
      · intro _
        rw [hb.1, hb.2.1]
        exact inter_empty_comm hF.2.2.1
      · intro h; exact absurd rfl h
      · intro _; rw [hb.2.1, hb.2.2.1]; exact hcross.2.1
      · intro _; rw [hb.2.1, hb.2.2.2]; exact hcross.2.2
    · refine fin4 (P := fun c => (2 : Fin 4) ≠ c →
          Bitset.inter (b 2) (b c) = Bitset.empty) ?_ ?_ ?_ ?_ c
      · intro _
        rw [hb.1, hb.2.2.1]
        exact inter_empty_comm hcross.1.1
      · intro _
        rw [hb.2.1, hb.2.2.1]
        exact inter_empty_comm hcross.2.1
      · intro h; exact absurd rfl h
      · intro _; rw [hb.2.2.1, hb.2.2.2]; exact hG.2.2.1
    · refine fin4 (P := fun c => (3 : Fin 4) ≠ c →
          Bitset.inter (b 3) (b c) = Bitset.empty) ?_ ?_ ?_ ?_ c
      · intro _
        rw [hb.1, hb.2.2.2]
        exact inter_empty_comm hcross.1.2
      · intro _
        rw [hb.2.1, hb.2.2.2]
        exact inter_empty_comm hcross.2.2
      · intro _
        rw [hb.2.2.1, hb.2.2.2]
        exact inter_empty_comm hG.2.2.1
      · intro h; exact absurd rfl h
  have htight : D15 (union4 b) := by
    have he : union4 b = W := by
      refine Bitset.ext (fun i => ?_)
      rw [union4, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hV]
    rwa [he]
  let A : D17 := ⟨b, his, hdis, htight⟩
  refine ⟨A, ?_⟩
  show union4 b = W
  refine Bitset.ext (fun i => ?_)
  rw [union4, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hV]

/-- `T26`.  Every AtlasInstance is the support of an AtlasPresentation. -/
public theorem T26 {W : Bitset} (hW : Atl W) : ∃ A : D17, V A = W :=
  presentation_of_atl hW

/-! ## Uniqueness of presentations up to reindexing -/

public theorem presentation_blk_inj (A : D17) {a b : Fin 4}
    (h : A.blk a = A.blk b) : a = b := by
  by_cases hab : a = b
  · exact hab
  have hd := A.disjoint a b hab
  have hu : Bitset.union (A.blk a) (A.blk b) = A.blk a := by
    rw [← h]
    refine Bitset.ext (fun i => ?_)
    rw [Bitset.mem_union]
    exact ⟨fun hi => hi.elim id id, fun hi => Or.inl hi⟩
  have hc := card_union_disj hd
  rw [hu, (A.isBlock a).2.1, (A.isBlock b).2.1] at hc
  omega

public theorem presentation_blk_ne (A : D17) {a b : Fin 4} (h : a ≠ b) :
    A.blk a ≠ A.blk b := fun he => h (presentation_blk_inj A he)

public theorem presentation_blkOf (A : D17) (a : Fin 4) :
    blkOf A.blk (A.blk a) = a := by
  refine fin4 (P := fun a => blkOf A.blk (A.blk a) = a) ?_ ?_ ?_ ?_ a
  · simp [blkOf]
  · rw [blkOf, if_neg (presentation_blk_ne A (by decide)), if_pos rfl]
  · rw [blkOf, if_neg (presentation_blk_ne A (by decide)),
      if_neg (presentation_blk_ne A (by decide)), if_pos rfl]
  · rw [blkOf, if_neg (presentation_blk_ne A (by decide)),
      if_neg (presentation_blk_ne A (by decide)),
      if_neg (presentation_blk_ne A (by decide))]

@[expose] public def presentationBlocks (A : D17) : List Bitset :=
  [A.blk 0, A.blk 1, A.blk 2, A.blk 3]

public theorem presentationBlocks_nodup (A : D17) : (presentationBlocks A).Nodup := by
  rw [presentationBlocks]
  apply List.nodup_cons.mpr
  refine ⟨?_, ?_⟩
  · intro h
    rcases List.mem_cons.mp h with h | h
    · exact presentation_blk_ne A (by decide) h
    · rcases List.mem_cons.mp h with h | h
      · exact presentation_blk_ne A (by decide) h
      · rcases List.mem_cons.mp h with h | h
        · exact presentation_blk_ne A (by decide) h
        · simp only [List.not_mem_nil] at h
  · apply List.nodup_cons.mpr
    refine ⟨?_, ?_⟩
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact presentation_blk_ne A (by decide) h
      · rcases List.mem_cons.mp h with h | h
        · exact presentation_blk_ne A (by decide) h
        · simp only [List.not_mem_nil] at h
    · apply List.nodup_cons.mpr
      refine ⟨?_, ?_⟩
      · intro h
        rcases List.mem_cons.mp h with h | h
        · exact presentation_blk_ne A (by decide) h
        · simp only [List.not_mem_nil] at h
      · exact List.nodup_cons.mpr ⟨fun h => by simp only [List.not_mem_nil] at h,
          List.nodup_nil⟩

public theorem presentationBlocks_length (A : D17) : (presentationBlocks A).length = 4 := rfl

public theorem mem_presentationBlocks {A : D17} {B : Bitset} :
    B ∈ presentationBlocks A ↔ ∃ a : Fin 4, B = A.blk a := by
  constructor
  · intro h
    rw [presentationBlocks] at h
    rcases List.mem_cons.mp h with h | h
    · exact ⟨0, h⟩
    · rcases List.mem_cons.mp h with h | h
      · exact ⟨1, h⟩
      · rcases List.mem_cons.mp h with h | h
        · exact ⟨2, h⟩
        · rcases List.mem_cons.mp h with h | h
          · exact ⟨3, h⟩
          · simp only [List.not_mem_nil] at h
  · rintro ⟨a, rfl⟩
    refine fin4 (P := fun a => A.blk a ∈ presentationBlocks A) ?_ ?_ ?_ ?_ a <;>
      simp [presentationBlocks]

public theorem presentation_block_contained (A : D17) (a : Fin 4) :
    ContainedBlock (V A) (A.blk a) := by
  refine ⟨A.isBlock a, fun i hi => ?_⟩
  exact (mem_union4 A.blk i).mpr ⟨a, hi⟩

public theorem presentation_complete {W : Bitset} (hW : Atl W) (A : D17)
    (hVA : V A = W) {B : Bitset} (hB : ContainedBlock W B) :
    ∃ a : Fin 4, B = A.blk a := by
  obtain ⟨L, hLnd, hLlen, hLmem⟩ := T25x hW
  have hsub : ∀ C, C ∈ presentationBlocks A → C ∈ L := by
    intro C hC
    obtain ⟨a, rfl⟩ := mem_presentationBlocks.mp hC
    apply (hLmem (A.blk a)).mpr
    rw [← hVA]
    exact presentation_block_contained A a
  have hback : ∀ C, C ∈ L → C ∈ presentationBlocks A := by
    intro C hC
    exact mem_of_subset_length_eq (presentationBlocks_nodup A) hsub (by
      rw [presentationBlocks_length, hLlen]) hC
  exact mem_presentationBlocks.mp (hback B ((hLmem B).mpr hB))

@[expose] public def presentationIndex (A B : D17) (i : Fin 4) : Fin 4 :=
  blkOf A.blk (B.blk i)

public theorem presentationIndex_spec {W : Bitset} (hW : Atl W) {A B : D17}
    (hA : V A = W) (hB : V B = W) (i : Fin 4) :
    A.blk (presentationIndex A B i) = B.blk i := by
  obtain ⟨a, ha⟩ := presentation_complete hW A hA
    (B := B.blk i) (hB ▸ presentation_block_contained B i)
  rw [presentationIndex, ha, presentation_blkOf]

public theorem presentationIndex_bijective {W : Bitset} (hW : Atl W) {A B : D17}
    (hA : V A = W) (hB : V B = W) :
    (∀ i, presentationIndex B A (presentationIndex A B i) = i)
      ∧ (∀ i, presentationIndex A B (presentationIndex B A i) = i) := by
  constructor
  · intro i
    apply presentation_blk_inj B
    rw [presentationIndex_spec hW hB hA, presentationIndex_spec hW hA hB]
  · intro i
    apply presentation_blk_inj A
    rw [presentationIndex_spec hW hA hB, presentationIndex_spec hW hB hA]

public theorem presentations_reindex {W : Bitset} (hW : Atl W) {A B : D17}
    (hA : V A = W) (hB : V B = W) :
    ∃ s : Perm 4, B.blk = reindex s A.blk ∧
      ∀ t : Perm 4, B.blk = reindex t A.blk → t = s := by
  have hi := presentationIndex_bijective hW hA hB
  let q : Perm 4 := ⟨presentationIndex A B, presentationIndex B A, hi.1, hi.2⟩
  refine ⟨q.inv, ?_, ?_⟩
  · funext i
    show B.blk i = A.blk (q.toFun i)
    exact (presentationIndex_spec hW hA hB i).symm
  · intro s hs
    have hinv : s.inv = q := by
      apply Perm.ext
      intro i
      apply presentation_blk_inj A
      have he := congrFun hs i
      change B.blk i = A.blk (s.invFun i) at he
      show A.blk (s.inv.toFun i) = A.blk (q.toFun i)
      rw [show s.inv.toFun i = s.invFun i from rfl, ← he]
      exact (presentationIndex_spec hW hA hB i).symm
    have he := congrArg Perm.inv hinv
    simpa [Perm.inv_inv] using he

/-- `T26x`.  The four blocks of an AtlasInstance are intrinsic: any two
ordered AtlasPresentations of the same support differ by one and only one
element of `Sym(4)`. -/
public theorem T26x {W : Bitset} (hW : Atl W) :
    ∀ A B : D17, V A = W → V B = W →
      ∃ s : Perm 4, B.blk = reindex s A.blk ∧
        ∀ t : Perm 4, B.blk = reindex t A.blk → t = s :=
  fun _ _ => presentations_reindex hW

public theorem union4_actPres (g : Perm 120) (b : Fin 4 → Bitset) :
    union4 (actPres g b) = actP g (union4 b) := by
  refine Bitset.ext (fun i => ?_)
  constructor
  · intro hi
    obtain ⟨a, ha⟩ := (mem_union4 (actPres g b) i).mp hi
    obtain ⟨u, hu, he⟩ := (mem_actP g (b a) i).mp ha
    exact (mem_actP g (union4 b) i).mpr
      ⟨u, (mem_union4 b u.val).mpr ⟨a, hu⟩, he⟩
  · intro hi
    obtain ⟨u, hu, he⟩ := (mem_actP g (union4 b) i).mp hi
    obtain ⟨a, ha⟩ := (mem_union4 b u.val).mp hu
    exact (mem_union4 (actPres g b) i).mpr
      ⟨a, (mem_actP g (b a) i).mpr ⟨u, ha, he⟩⟩

@[expose] public def presentationImage (g : Perm 120) (hg : D21 g) (A : D17) : D17 where
  blk := actPres g A.blk
  isBlock := fun a => aut_block hg (A.isBlock a)
  disjoint := by
    intro a b hab
    change Bitset.inter (actP g (A.blk a)) (actP g (A.blk b)) = Bitset.empty
    rw [← actP_inter, A.disjoint a b hab, actP_empty]
  tight := by
    rw [union4_actPres]
    exact aut_tight hg A.tight

public theorem V_presentationImage (g : Perm 120) (hg : D21 g) (A : D17) :
    V (presentationImage g hg A) = actP g (V A) := by
  change union4 (actPres g A.blk) = actP g (union4 A.blk)
  exact union4_actPres g A.blk

public theorem edges_image {g : Perm 120} (hg : D21 g) (S T : Bitset) :
    edges (actP g S) (actP g T) = edges S T := by
  show Vec.sumNat (fun u : K => if u.val ∈ actP g S then D14 (actP g T) u else 0) = _
  rw [← sumK_reindex g
    (fun u : K => if u.val ∈ actP g S then D14 (actP g T) u else 0)]
  apply Vec.sumNat_congr
  intro u
  have himg := mem_actP_image_iff g S u
  by_cases hu : u.val ∈ S
  · rw [if_pos (himg.mpr hu), if_pos hu, D14_image hg]
  · rw [if_neg (fun h => hu (himg.mp h)), if_neg hu]

public theorem D19_presentationImage (g : Perm 120) (hg : D21 g) (A : D17)
    (a b : Fin 4) :
    D19 (presentationImage g hg A) a b = D19 A a b := by
  change ((edges (actP g (A.blk a)) (actP g (A.blk b)) : Nat) : Rat) /
      ((Bitset.card (actP g (A.blk a)) : Nat) : Rat) =
    ((edges (A.blk a) (A.blk b) : Nat) : Rat) /
      ((Bitset.card (A.blk a) : Nat) : Rat)
  rw [edges_image hg, (aut_block hg (A.isBlock a)).2.1, (A.isBlock a).2.1]

@[expose] public def reindexedPartner (s : Perm 4) (a : Fin 4) : Fin 4 :=
  s.toFun (nullPartner (s.invFun a))

public theorem reindexedPartner_involutive (s : Perm 4) (a : Fin 4) :
    reindexedPartner s (reindexedPartner s a) = a := by
  simp only [reindexedPartner, s.left_inv, T17.2.1, s.right_inv]

public theorem reindexedPartner_ne (s : Perm 4) (a : Fin 4) :
    reindexedPartner s a ≠ a := by
  intro h
  have hi := congrArg s.invFun h
  simp only [reindexedPartner, s.left_inv] at hi
  exact T17.2.2 (s.invFun a) hi

/-- `T26a`.  On every presentation of an AtlasInstance, the zero entries of
the block-average matrix form a fixed-point-free involution: the null relation
is a perfect matching of the four blocks. -/
public theorem T26a {W : Bitset} (hW : Atl W) (A : D17) (hA : V A = W) :
    ∃ p : Fin 4 → Fin 4,
      (∀ a b, D19 A a b = 0 ↔ b = p a)
        ∧ (∀ a, p (p a) = a) ∧ (∀ a, p a ≠ a) := by
  obtain ⟨g, hg, hWg⟩ := (T27 W).mp hW
  let B := presentationImage g hg Blocks.A0
  have hB : V B = W := by
    rw [V_presentationImage, W0_eq, hWg]
  obtain ⟨s, hs, _⟩ := presentations_reindex hW hB hA
  refine ⟨reindexedPartner s, ?_, reindexedPartner_involutive s,
    reindexedPartner_ne s⟩
  intro a b
  have hsa := congrFun hs a
  have hsb := congrFun hs b
  have hq : D19 A a b = D19 Blocks.A0 (s.invFun a) (s.invFun b) := by
    unfold D19
    rw [hsa, hsb]
    exact D19_presentationImage g hg Blocks.A0 (s.invFun a) (s.invFun b)
  rw [hq, T17.1]
  constructor
  · intro h
    have hi := congrArg s.toFun h
    simpa only [s.right_inv, reindexedPartner] using hi
  · intro h
    have hi := congrArg s.invFun h
    simpa [reindexedPartner, s.left_inv] using hi

/-! ## The twenty-four orderings of the intrinsic four blocks -/

@[expose] public def permCode4 (s : Perm 4) : Nat :=
  (s.toFun 0).val + 4 * (s.toFun 1).val + 16 * (s.toFun 2).val
    + 64 * (s.toFun 3).val

@[expose] public def codeMap4 (n : Nat) (i : Fin 4) : Fin 4 :=
  if i = 0 then ⟨n % 4, Nat.mod_lt _ (by decide)⟩
  else if i = 1 then ⟨n / 4 % 4, Nat.mod_lt _ (by decide)⟩
  else if i = 2 then ⟨n / 16 % 4, Nat.mod_lt _ (by decide)⟩
  else ⟨n / 64 % 4, Nat.mod_lt _ (by decide)⟩

@[expose] public def codePerm4 (n : Nat) : Perm 4 := permOf4 (codeMap4 n)

public theorem codeMap4_permCode4 (s : Perm 4) (i : Fin 4) :
    codeMap4 (permCode4 s) i = s.toFun i := by
  refine fin4 (P := fun i => codeMap4 (permCode4 s) i = s.toFun i) ?_ ?_ ?_ ?_ i
  · apply Fin.eq_of_val_eq
    rw [codeMap4, if_pos rfl]
    change permCode4 s % 4 = (s.toFun 0).val
    unfold permCode4
    have h0 := (s.toFun 0).isLt
    have h1 := (s.toFun 1).isLt
    have h2 := (s.toFun 2).isLt
    have h3 := (s.toFun 3).isLt
    omega
  · apply Fin.eq_of_val_eq
    rw [codeMap4, if_neg (by decide), if_pos rfl]
    change permCode4 s / 4 % 4 = (s.toFun 1).val
    unfold permCode4
    have h0 := (s.toFun 0).isLt
    have h1 := (s.toFun 1).isLt
    have h2 := (s.toFun 2).isLt
    have h3 := (s.toFun 3).isLt
    omega
  · apply Fin.eq_of_val_eq
    rw [codeMap4, if_neg (by decide), if_neg (by decide), if_pos rfl]
    change permCode4 s / 16 % 4 = (s.toFun 2).val
    unfold permCode4
    have h0 := (s.toFun 0).isLt
    have h1 := (s.toFun 1).isLt
    have h2 := (s.toFun 2).isLt
    have h3 := (s.toFun 3).isLt
    omega
  · apply Fin.eq_of_val_eq
    rw [codeMap4, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    change permCode4 s / 64 % 4 = (s.toFun 3).val
    unfold permCode4
    have h0 := (s.toFun 0).isLt
    have h1 := (s.toFun 1).isLt
    have h2 := (s.toFun 2).isLt
    have h3 := (s.toFun 3).isLt
    omega

public theorem codePerm4_permCode4 (s : Perm 4) : codePerm4 (permCode4 s) = s := by
  rw [codePerm4, show codeMap4 (permCode4 s) = s.toFun from
    funext (codeMap4_permCode4 s), permOf4_of_perm]

public theorem permCode4_lt (s : Perm 4) : permCode4 s < 256 := by
  have h0 := (s.toFun 0).isLt
  have h1 := (s.toFun 1).isLt
  have h2 := (s.toFun 2).isLt
  have h3 := (s.toFun 3).isLt
  unfold permCode4
  omega

@[expose] public def symFourList : List (Perm 4) :=
  dedup ((List.range 256).map codePerm4)

public theorem symFourList_nodup : symFourList.Nodup := nodup_dedup

set_option maxHeartbeats 4000000 in
public theorem symFourList_length : symFourList.length = 24 := by decide +kernel

public theorem mem_symFourList (s : Perm 4) : s ∈ symFourList := by
  rw [symFourList, mem_dedup, List.mem_map]
  exact ⟨permCode4 s, List.mem_range.mpr (permCode4_lt s), codePerm4_permCode4 s⟩

public theorem union4_reindex (s : Perm 4) (b : Fin 4 → Bitset) :
    union4 (reindex s b) = union4 b := by
  refine Bitset.ext (fun i => ?_)
  rw [mem_union4, mem_union4]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨s.invFun a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨s.toFun a, ?_⟩
    simpa [reindex, s.left_inv]

@[expose] public def reindexPresentation (s : Perm 4) (A : D17) : D17 where
  blk := reindex s A.blk
  isBlock := fun a => A.isBlock (s.invFun a)
  disjoint := by
    intro a b hab
    apply A.disjoint
    intro he
    apply hab
    calc
      a = s.toFun (s.invFun a) := (s.right_inv a).symm
      _ = s.toFun (s.invFun b) := congrArg s.toFun he
      _ = b := s.right_inv b
  tight := by
    rw [union4_reindex]
    exact A.tight

public theorem V_reindexPresentation (s : Perm 4) (A : D17) :
    V (reindexPresentation s A) = V A := union4_reindex s A.blk

public theorem reindex_free (A : D17) {s t : Perm 4}
    (h : reindex s A.blk = reindex t A.blk) : s = t := by
  have hi : s.inv = t.inv := by
    apply Perm.ext
    intro i
    apply presentation_blk_inj A
    exact congrFun h i
  have := congrArg Perm.inv hi
  simpa [Perm.inv_inv] using this

public theorem presentation_fibre_24 {W : Bitset} (hW : Atl W) (A : D17)
    (hA : V A = W) :
    ∃ L : List (Fin 4 → Bitset), L.Nodup ∧ L.length = 24 ∧
      ∀ b, b ∈ L ↔ ∃ B : D17, V B = W ∧ B.blk = b := by
  let L := symFourList.map (fun s => reindex s A.blk)
  refine ⟨L, ?_, by simp [L, symFourList_length], fun b => ?_⟩
  · exact nodup_map_on (fun s => reindex s A.blk) symFourList symFourList_nodup
      (fun s _ t _ he => reindex_free A he)
  · constructor
    · intro hb
      obtain ⟨s, hs, he⟩ := List.mem_map.mp hb
      rw [← he]
      exact ⟨reindexPresentation s A, by rw [V_reindexPresentation, hA], rfl⟩
    · rintro ⟨B, hB, rfl⟩
      obtain ⟨s, hs, _⟩ := presentations_reindex hW hA hB
      exact List.mem_map.mpr ⟨s, mem_symFourList s, hs.symm⟩

/-- `T26b`.  The support map has exactly `24 = |Sym(4)|` ordered
presentations over each of the `75600` AtlasInstances, hence `1814400`
presentation/support pairs in total. -/
public theorem T26b :
    (∃ O : List Bitset, O.Nodup ∧ O.length = 75600 ∧
      (∀ W, W ∈ O ↔ Atl W))
      ∧ (∀ W, Atl W → ∃ L : List (Fin 4 → Bitset),
        L.Nodup ∧ L.length = 24 ∧
          ∀ b, b ∈ L ↔ ∃ A : D17, V A = W ∧ A.blk = b)
      ∧ 75600 * 24 = 1814400 := by
  refine ⟨T24, ?_, by decide⟩
  intro W hW
  obtain ⟨A, hA⟩ := T26 hW
  exact presentation_fibre_24 hW A hA

/-! ## Transport of presentation stabilisers -/

/-- The concrete ordered witness used for presentation-level transport.  It
has the same four checked blocks as the document's witness presentation, but
keeps its block projection definitionally visible to downstream transport
arguments. -/
@[expose] public def canonicalPresentation : D17 where
  blk := Blocks.blkSet
  isBlock := Blocks.blkIsBlock
  disjoint := Blocks.blkDisjoint
  tight := Blocks.tight_of_tightOK Blocks.tightComp

public theorem V_canonicalPresentation : V canonicalPresentation = W0 := by
  simp only [V, canonicalPresentation, W0]

public theorem stabPres_reindex_iff (s : Perm 4) (b : Fin 4 → Bitset)
    (g : Perm 120) : stabPres (reindex s b) g ↔ stabPres b g := by
  constructor
  · rintro ⟨hg, hfix⟩
    refine ⟨hg, fun a => ?_⟩
    have h := hfix (s.toFun a)
    simpa [reindex, s.left_inv a] using h
  · rintro ⟨hg, hfix⟩
    exact ⟨hg, fun a => by simpa [reindex] using hfix (s.invFun a)⟩

public theorem stabPres_conjugate_iff {g k : Perm 120} (hg : D21 g)
    {b : Fin 4 → Bitset} (hb : ∀ a, ClassSet (b a)) :
    stabPres (actPres g b) (conjugate g k) ↔ stabPres b k := by
  constructor
  · rintro ⟨hc, hfix⟩
    refine ⟨?_, fun a => ?_⟩
    · have hc' : D21 (conjugate g.inv (conjugate g k)) :=
        Perm.Gen.comp_mem (Perm.Gen.inv_mem hg) (Perm.Gen.comp_mem hc hg)
      have he : conjugate g.inv (conjugate g k) = k := by
        simpa only [Perm.inv_inv] using conjugate_inv g.inv k
      rwa [he] at hc'
    · have hEq : actP g (actP k (b a)) = actP g (b a) := by
        simpa only [actPres, conjugate, actP_comp, actP_inv g (hb a)] using hfix a
      exact actP_inj g (classSet_actP k (b a)) (hb a) hEq
  · rintro ⟨hk, hfix⟩
    refine ⟨Perm.Gen.comp_mem hg (Perm.Gen.comp_mem hk (Perm.Gen.inv_mem hg)), fun a => ?_⟩
    simp only [actPres, conjugate, actP_comp]
    rw [actP_inv g (hb a), hfix a]

public theorem stab_order_image {g : Perm 120} (hg : D21 g) :
    HasOrderP (stabPres (actPres g Blocks.blkSet)) 576 := by
  obtain ⟨L, hnd, hmem, hlen⟩ := T39p
  refine ⟨L.map (conjugate g), ?_, ?_, by rw [List.length_map, hlen]⟩
  · exact nodup_map_on (conjugate g) L hnd
      (fun a _ b _ he => conjugate_inj g he)
  · intro k
    constructor
    · intro hk
      obtain ⟨l, hl, he⟩ := List.mem_map.mp hk
      rw [← he]
      exact (stabPres_conjugate_iff hg (fun a => (Blocks.blkIsBlock a).1)).mpr
        ((hmem l).mp hl)
    · intro hk
      let l := conjugate g.inv k
      have hl : stabPres Blocks.blkSet l := by
        apply (stabPres_conjugate_iff hg (fun a => (Blocks.blkIsBlock a).1)).mp
        rw [conjugate_inv]
        exact hk
      exact List.mem_map.mpr ⟨l, (hmem l).mpr hl, conjugate_inv g k⟩

/-- `T39`.  Every ordered presentation of an AtlasInstance has pointwise
block stabiliser of order `576`; the witness Schreier chain is transported by
conjugation, and reindexing does not change the subgroup. -/
public theorem T39 {W : Bitset} (hW : Atl W) (A : D17) (hA : V A = W) :
    HasOrderP (stabPres A.blk) 576 := by
  obtain ⟨g, hg, hWg⟩ := (T27 W).mp hW
  let B := presentationImage g hg canonicalPresentation
  have hBblk : B.blk = actPres g Blocks.blkSet := by
    simp only [B, presentationImage, canonicalPresentation]
  have hB : V B = W := by
    rw [V_presentationImage, V_canonicalPresentation, hWg]
  obtain ⟨s, hs, _⟩ := presentations_reindex hW hB hA
  obtain ⟨L, hnd, hmem, hlen⟩ := stab_order_image hg
  refine ⟨L, hnd, fun k => (hmem k).trans ?_, hlen⟩
  rw [← hBblk]
  rw [hs]
  exact (stabPres_reindex_iff s B.blk k).symm

public theorem conjugate_apply (g k : Perm 120) (u : K) :
    (conjugate g k).toFun (g.toFun u) = g.toFun (k.toFun u) := by
  show g.toFun (k.toFun (g.invFun (g.toFun u))) = _
  rw [g.left_inv]

public theorem fixesBlock_conjugate_iff (g k : Perm 120) (B : Bitset) :
    FixesBlock (actP g B) (conjugate g k) ↔ FixesBlock B k := by
  constructor
  · intro h u hu
    apply Perm.toFun_injective (p := g)
    rw [← conjugate_apply]
    apply h (g.toFun u)
    exact (mem_actP_image_iff g B u).mpr hu
  · intro h v hv
    let u := g.invFun v
    have hvu : g.toFun u = v := g.right_inv v
    rw [← hvu, conjugate_apply, h u]
    exact (mem_actP_image_iff g B u).mp (hvu ▸ hv)

/-- `T52`.  The kernel acts faithfully on any one block of any presentation:
fixing the twelve classes of a chosen block pointwise forces the ambient
automorphism to be the identity. -/
public theorem T52 {W : Bitset} (hW : Atl W) (A : D17) (hA : V A = W)
    (a : Fin 4) {k : Perm 120} (hk : stabPres A.blk k)
    (hfix : FixesBlock (A.blk a) k) : k = Perm.one 120 := by
  obtain ⟨g, hg, hWg⟩ := (T27 W).mp hW
  let B := presentationImage g hg canonicalPresentation
  have hBblk : B.blk = actPres g Blocks.blkSet := by
    simp only [B, presentationImage, canonicalPresentation]
  have hB : V B = W := by
    rw [V_presentationImage, V_canonicalPresentation, hWg]
  obtain ⟨s, hs, _⟩ := presentations_reindex hW hB hA
  have hkB : stabPres B.blk k := by
    rw [hs] at hk
    exact (stabPres_reindex_iff s B.blk k).mp hk
  have hkImage : stabPres (actPres g Blocks.blkSet) k := by
    rw [← hBblk]
    exact hkB
  let l := conjugate g.inv k
  have hl : stabPres Blocks.blkSet l := by
    apply (stabPres_conjugate_iff hg (fun i => (Blocks.blkIsBlock i).1)).mp
    rw [conjugate_inv]
    exact hkImage
  have hla : FixesBlock (Blocks.blkSet (s.invFun a)) l := by
    apply (fixesBlock_conjugate_iff g l (Blocks.blkSet (s.invFun a))).mp
    rw [conjugate_inv]
    have hsa := congrFun hs a
    have hfixImage : FixesBlock (actP g (Blocks.blkSet (s.invFun a))) k := by
      have hAct : actPres g Blocks.blkSet (s.invFun a) =
          actP g (Blocks.blkSet (s.invFun a)) := by
        simp only [actPres]
      rw [← hAct, ← congrFun hBblk (s.invFun a)]
      change A.blk a = B.blk (s.invFun a) at hsa
      rw [← hsa]
      exact hfix
    exact hfixImage
  have hlone := kernel_faithful_on_witness_block (s.invFun a)
    ((stabPres_eq l).mp hl) hla
  have hc := congrArg (conjugate g) hlone
  have hleft : conjugate g l = k := by
    simpa only [l] using conjugate_inv g k
  rw [hleft, conjugate_one] at hc
  exact hc

/-! ## The signed block-automorphism cover -/

/-- Order for a predicate on signed class actions.  The Boolean coordinate is
the central choice of lift from a permutation of root classes to roots. -/
@[expose] public def HasOrderSigned
    (P : Bool × Perm 120 → Prop) (n : Nat) : Prop :=
  ∃ L : List (Bool × Perm 120), L.Nodup ∧
    (∀ z : Bool × Perm 120, z ∈ L ↔ P z) ∧ L.length = n

/-- The concrete signed model of the automorphism group of one displayed
block.  Its class action is the presentation kernel; its Boolean coordinate
records the two root actions differing by the central map `-I`. -/
@[expose] public def BlockAutCover (z : Bool × Perm 120) : Prop :=
  D29 Blocks.blkSet W0 z.2

/-- The central sign changes the lift and leaves its class action fixed. -/
@[expose] public def blockAutSign (z : Bool × Perm 120) : Bool × Perm 120 :=
  (!z.1, z.2)

public theorem blockAutCover_order : HasOrderSigned BlockAutCover 1152 := by
  obtain ⟨L, hnd, hmem, hlen⟩ := T32
  let L0 := L.map (fun g => (false, g))
  let L1 := L.map (fun g => (true, g))
  refine ⟨L0 ++ L1, ?_, fun z => ?_, ?_⟩
  · have h0 : L0.Nodup := nodup_map_on (fun g => (false, g)) L hnd
      (fun a _ b _ he => congrArg Prod.snd he)
    have h1 : L1.Nodup := nodup_map_on (fun g => (true, g)) L hnd
      (fun a _ b _ he => congrArg Prod.snd he)
    apply List.nodup_append.mpr
    refine ⟨h0, h1, ?_⟩
    intro z hz0 w hz1 hezw
    obtain ⟨g, _, he0⟩ := List.mem_map.mp hz0
    obtain ⟨k, _, he1⟩ := List.mem_map.mp hz1
    have he : (false, g) = (true, k) := he0.trans (hezw.trans he1.symm)
    exact Bool.noConfusion (congrArg Prod.fst he)
  · constructor
    · intro hz
      rcases List.mem_append.mp hz with hz | hz
      · obtain ⟨g, hg, he⟩ := List.mem_map.mp hz
        rw [← he]
        exact (hmem g).mp hg
      · obtain ⟨g, hg, he⟩ := List.mem_map.mp hz
        rw [← he]
        exact (hmem g).mp hg
    · intro hz
      rcases z with ⟨b, g⟩
      cases b with
      | false =>
          exact List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨g, (hmem g).mpr hz, rfl⟩))
      | true =>
          exact List.mem_append.mpr (Or.inr
            (List.mem_map.mpr ⟨g, (hmem g).mpr hz, rfl⟩))
  · simp only [L0, L1, List.length_append, List.length_map, hlen]

public theorem blockAutSign_fibre (z : Bool × Perm 120) :
    blockAutSign (blockAutSign z) = z ∧
      (blockAutSign z).2 = z.2 := by
  rcases z with ⟨b, g⟩
  cases b <;> exact ⟨rfl, rfl⟩

public theorem blockAutCover_fibres : ∀ k : Perm 120,
    D29 Blocks.blkSet W0 k →
      BlockAutCover (false, k) ∧ BlockAutCover (true, k)
        ∧ (∀ z : Bool × Perm 120, BlockAutCover z → z.2 = k →
          z = (false, k) ∨ z = (true, k)) := by
  intro k hk
  refine ⟨hk, hk, fun z _ hz => ?_⟩
  rcases z with ⟨b, g⟩
  cases b with
  | false => exact Or.inl (Prod.ext rfl hz)
  | true => exact Or.inr (Prod.ext rfl hz)

/-- `T53`.  The automorphism group of a displayed block is the signed double
cover of the `576`-element presentation kernel: it has order `1152`, the
central sign is a fixed-point-free two-fold lift over every kernel action, and
forgetting that sign gives exactly the kernel, i.e. the quotient by `{±I}`. -/
public theorem T53 :
    HasOrderSigned BlockAutCover 1152
      ∧ HasOrderP (D29 Blocks.blkSet W0) 576
      ∧ (∀ z : Bool × Perm 120, BlockAutCover z →
        BlockAutCover (blockAutSign z)
          ∧ blockAutSign (blockAutSign z) = z
          ∧ (blockAutSign z).2 = z.2)
      ∧ (∀ k : Perm 120, D29 Blocks.blkSet W0 k →
        BlockAutCover (false, k) ∧ BlockAutCover (true, k)
          ∧ (∀ z : Bool × Perm 120, BlockAutCover z → z.2 = k →
            z = (false, k) ∨ z = (true, k))) := by
  refine ⟨blockAutCover_order, T32, ?_, blockAutCover_fibres⟩
  intro z hz
  exact ⟨hz, (blockAutSign_fibre z).1, (blockAutSign_fibre z).2⟩

end UorAtlas.Closure

end
