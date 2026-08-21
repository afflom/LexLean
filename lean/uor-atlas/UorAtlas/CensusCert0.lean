module

public import Init
public import UorAtlas.CensusClosure

public section

namespace UorAtlas.Census

set_option maxHeartbeats 4000000 in
public theorem gramWin0 : gramRange 0 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem gramWin1 : gramRange 1000 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem gramWin2 : gramRange 2000 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem gramWin3 : gramRange 3000 1000 = true := by decide +kernel

end UorAtlas.Census

end
