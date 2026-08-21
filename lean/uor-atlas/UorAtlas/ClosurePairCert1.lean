module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert1 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 100) 100 = 9432 := by
  decide +kernel
end UorAtlas.Closure
end
