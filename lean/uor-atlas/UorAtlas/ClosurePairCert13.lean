module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert13 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 1300) 100 = 1318 := by
  decide +kernel
end UorAtlas.Closure
end
