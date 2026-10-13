import Mathlib
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand

namespace ServiceParts.StockLevels

theorem expected_on_hand (d : CompoundPoissonDemand) (s : ℕ) :
    d.expectedOnHand s = (s : ℝ) - d.lam * d.tbar * d.ubar + d.backorders s := by sorry

end ServiceParts.StockLevels

