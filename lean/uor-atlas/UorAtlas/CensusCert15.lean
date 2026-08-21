module
public import Init
public import UorAtlas.CensusClosure
public section
namespace UorAtlas.Census
set_option maxHeartbeats 4000000 in
public theorem gramWin15 : gramRange 15000 625 = true := by decide +kernel
end UorAtlas.Census
end
