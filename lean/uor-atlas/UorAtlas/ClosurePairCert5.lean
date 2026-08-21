module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert5 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 500) 100 = 6086 := by
  decide +kernel
end UorAtlas.Closure
end
