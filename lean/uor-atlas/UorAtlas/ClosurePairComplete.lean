module

public import Init
public import UorAtlas.ClosurePairCert0
public import UorAtlas.ClosurePairCert1
public import UorAtlas.ClosurePairCert2
public import UorAtlas.ClosurePairCert3
public import UorAtlas.ClosurePairCert4
public import UorAtlas.ClosurePairCert5
public import UorAtlas.ClosurePairCert6
public import UorAtlas.ClosurePairCert7
public import UorAtlas.ClosurePairCert8
public import UorAtlas.ClosurePairCert9
public import UorAtlas.ClosurePairCert10
public import UorAtlas.ClosurePairCert11
public import UorAtlas.ClosurePairCert12
public import UorAtlas.ClosurePairCert13
public import UorAtlas.ClosurePairCert14
public import UorAtlas.ClosurePairCert15

public section

namespace UorAtlas.Closure

public theorem atlasPairCount_cert :
    atlasPairCountTake frameSupportRows frameSupportRows 1575 = 75600 := by
  have h0 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 0) 100 1475
  have h1 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 100) 100 1375
  have h2 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 200) 100 1275
  have h3 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 300) 100 1175
  have h4 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 400) 100 1075
  have h5 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 500) 100 975
  have h6 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 600) 100 875
  have h7 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 700) 100 775
  have h8 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 800) 100 675
  have h9 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 900) 100 575
  have h10 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 1000) 100 475
  have h11 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 1100) 100 375
  have h12 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 1200) 100 275
  have h13 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 1300) 100 175
  have h14 := atlasPairCountTake_append frameSupportRows
    (frameSupportRows.drop 1400) 100 75
  simp only [List.drop_zero, List.drop_drop, Nat.reduceAdd] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  have c0 := atlasPairCountCert0
  have c1 := atlasPairCountCert1
  have c2 := atlasPairCountCert2
  have c3 := atlasPairCountCert3
  have c4 := atlasPairCountCert4
  have c5 := atlasPairCountCert5
  have c6 := atlasPairCountCert6
  have c7 := atlasPairCountCert7
  have c8 := atlasPairCountCert8
  have c9 := atlasPairCountCert9
  have c10 := atlasPairCountCert10
  have c11 := atlasPairCountCert11
  have c12 := atlasPairCountCert12
  have c13 := atlasPairCountCert13
  have c14 := atlasPairCountCert14
  have c15 := atlasPairCountCert15
  simp only [List.drop_zero] at c0
  omega

public theorem atlasPairs_length : atlasPairs.length = 75600 :=
  atlasPairs_length_eq_count.trans atlasPairCount_cert

public theorem atlasSupports_length : atlasSupports.length = 75600 := by
  rw [atlasSupports, List.length_map, atlasPairs_length]

end UorAtlas.Closure

end
