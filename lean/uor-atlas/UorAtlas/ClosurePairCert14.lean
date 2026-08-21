module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert14 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 1400) 100 = 620 := by
  decide +kernel
end UorAtlas.Closure
end
