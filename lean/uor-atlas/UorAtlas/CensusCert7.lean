module
public import Init
public import UorAtlas.CensusCert70
public import UorAtlas.CensusCert71
public import UorAtlas.CensusCert72
public import UorAtlas.CensusCert73
public import UorAtlas.CensusCert74
public import UorAtlas.CensusCert75
public import UorAtlas.CensusCert76
public import UorAtlas.CensusCert77
public import UorAtlas.CensusCert78
public import UorAtlas.CensusCert79
public section
namespace UorAtlas.Census
public theorem gramWin7 : gramRange 7000 1000 = true := by
  simpa using gramRange_append gramWin70
    (gramRange_append gramWin71
      (gramRange_append gramWin72
        (gramRange_append gramWin73
          (gramRange_append gramWin74
            (gramRange_append gramWin75
              (gramRange_append gramWin76
                (gramRange_append gramWin77
                  (gramRange_append gramWin78 gramWin79))))))))
end UorAtlas.Census
end
