module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert8 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 800) 100 = 4512 := by
  decide +kernel
end UorAtlas.Closure
end
