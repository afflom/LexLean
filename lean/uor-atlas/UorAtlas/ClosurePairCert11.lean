module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert11 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 1100) 100 = 2030 := by
  decide +kernel
end UorAtlas.Closure
end
