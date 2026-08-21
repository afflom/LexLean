module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert15 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 1500) 75 = 60 := by
  decide +kernel
end UorAtlas.Closure
end
