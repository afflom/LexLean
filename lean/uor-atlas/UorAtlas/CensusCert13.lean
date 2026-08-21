module
public import Init
public import UorAtlas.CensusClosure
public section
namespace UorAtlas.Census
set_option maxHeartbeats 4000000 in
public theorem gramWin13 : gramRange 13000 1000 = true := by decide +kernel
end UorAtlas.Census
end
