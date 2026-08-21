module
public import Init
public import UorAtlas.CensusClosure
public section
namespace UorAtlas.Census
set_option maxHeartbeats 4000000 in
public theorem gramWin6 : gramRange 6000 1000 = true := by decide +kernel
end UorAtlas.Census
end
