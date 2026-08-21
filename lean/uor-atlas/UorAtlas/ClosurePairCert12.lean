module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert12 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 1200) 100 = 1494 := by
  decide +kernel
end UorAtlas.Closure
end
