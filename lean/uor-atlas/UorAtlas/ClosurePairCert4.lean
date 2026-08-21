module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert4 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 400) 100 = 6570 := by
  decide +kernel
end UorAtlas.Closure
end
