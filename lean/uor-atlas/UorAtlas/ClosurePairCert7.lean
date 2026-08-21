module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert7 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 700) 100 = 5148 := by
  decide +kernel
end UorAtlas.Closure
end
