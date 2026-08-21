module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert3 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 300) 100 = 7944 := by
  decide +kernel
end UorAtlas.Closure
end
