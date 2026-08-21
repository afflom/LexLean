module
public import Init
public import UorAtlas.ClosurePairs
public section
namespace UorAtlas.Closure
set_option maxHeartbeats 4000000 in
public theorem atlasPairCountCert6 :
    atlasPairCountTake frameSupportRows (frameSupportRows.drop 600) 100 = 5580 := by
  decide +kernel
end UorAtlas.Closure
end
