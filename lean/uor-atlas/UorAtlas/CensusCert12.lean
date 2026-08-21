module
public import Init
public import UorAtlas.CensusClosure
public section
namespace UorAtlas.Census
set_option maxHeartbeats 4000000 in
public theorem gramWin12 : gramRange 12000 1000 = true := by decide +kernel
end UorAtlas.Census
end
