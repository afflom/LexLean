module

public import Init
public import UorAtlas.CensusCert0
public import UorAtlas.CensusCert4
public import UorAtlas.CensusCert5
public import UorAtlas.CensusCert6
public import UorAtlas.CensusCert7
public import UorAtlas.CensusCert8
public import UorAtlas.CensusCert9
public import UorAtlas.CensusCert10
public import UorAtlas.CensusCert11
public import UorAtlas.CensusCert12
public import UorAtlas.CensusCert13
public import UorAtlas.CensusCert14
public import UorAtlas.CensusCert15

public section

namespace UorAtlas.Census

open UorAtlas.Prelude
open UorAtlas.Blocks

public theorem gramCases : ∀ g, g < 15625 → gramCaseOK g = true := by
  intro g hg
  by_cases h0 : g < 1000
  · exact gramRange_true gramWin0 (by omega) (by omega)
  by_cases h1 : g < 2000
  · exact gramRange_true gramWin1 (by omega) (by omega)
  by_cases h2 : g < 3000
  · exact gramRange_true gramWin2 (by omega) (by omega)
  by_cases h3 : g < 4000
  · exact gramRange_true gramWin3 (by omega) (by omega)
  by_cases h4 : g < 5000
  · exact gramRange_true gramWin4 (by omega) (by omega)
  by_cases h5 : g < 6000
  · exact gramRange_true gramWin5 (by omega) (by omega)
  by_cases h6 : g < 7000
  · exact gramRange_true gramWin6 (by omega) (by omega)
  by_cases h7 : g < 8000
  · exact gramRange_true gramWin7 (by omega) (by omega)
  by_cases h8 : g < 9000
  · exact gramRange_true gramWin8 (by omega) (by omega)
  by_cases h9 : g < 10000
  · exact gramRange_true gramWin9 (by omega) (by omega)
  by_cases h10 : g < 11000
  · exact gramRange_true gramWin10 (by omega) (by omega)
  by_cases h11 : g < 12000
  · exact gramRange_true gramWin11 (by omega) (by omega)
  by_cases h12 : g < 13000
  · exact gramRange_true gramWin12 (by omega) (by omega)
  by_cases h13 : g < 14000
  · exact gramRange_true gramWin13 (by omega) (by omega)
  by_cases h14 : g < 15000
  · exact gramRange_true gramWin14 (by omega) (by omega)
  · exact gramRange_true gramWin15 (by omega) (by omega)

/-- Every abstract block occurs exactly once in the exhibited table. -/
public theorem block_census_complete {B : Bitset} (hB : D16 B) :
    ∃ i : Nat, i < 3150 ∧ blkAt i = B :=
  block_in_table hB gramCases

/-! ## `T22`: the complete block census -/

/-- `T22`.  The displayed table is a bijective enumeration of `Blk`, hence
`|Blk| = 3150`: every entry is a block, distinct indices give distinct blocks,
and every block occurs. -/
public theorem T22 :
    (∀ i : Nat, i < 3150 → Blk (blkAt i))
      ∧ (∀ i j : Nat, i < 3150 → j < 3150 → i ≠ j → blkAt i ≠ blkAt j)
      ∧ (∀ B : Bitset, Blk B → ∃ i : Nat, i < 3150 ∧ blkAt i = B) :=
  ⟨blkExhibit.1, blkExhibit.2, fun _ hB => block_census_complete hB⟩

end UorAtlas.Census

end
