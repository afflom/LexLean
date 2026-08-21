module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert2 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 200) 100 = 9376 := by
  decide +kernel
end UorAtlas.Closure
end
