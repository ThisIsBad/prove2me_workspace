import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand

namespace ServiceParts.StockLevels

theorem backorder_differences (d : CompoundPoissonDemand) (s : ℕ) :
    fdiff d.backorders s = -(1 - d.readyRate s) ∧
    fdiff2 d.backorders s = d.pmf (s + 1) ∧
    0 ≤ fdiff2 d.backorders s ∧
    (d.u 1 = 1 → fdiff d.backorders s < 0 ∧ 0 < fdiff2 d.backorders s) := by sorry

end ServiceParts.StockLevels

