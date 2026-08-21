module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert0 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 0) 100 = 9576 := by
  decide +kernel
end UorAtlas.Closure
end
