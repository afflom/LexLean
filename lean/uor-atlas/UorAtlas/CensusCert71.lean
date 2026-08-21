module
public import Init
public import UorAtlas.CensusClosure
public section
namespace UorAtlas.Census
set_option maxHeartbeats 4000000 in
public theorem gramWin71 : gramRange 7100 100 = true := by decide +kernel
end UorAtlas.Census
end
