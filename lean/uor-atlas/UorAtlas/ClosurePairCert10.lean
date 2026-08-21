module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert10 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 1000) 100 = 2738 := by
  decide +kernel
end UorAtlas.Closure
end
