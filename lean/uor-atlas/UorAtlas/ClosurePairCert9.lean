module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert9 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 900) 100 = 3116 := by
  decide +kernel
end UorAtlas.Closure
end
