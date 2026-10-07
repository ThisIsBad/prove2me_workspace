import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, p. 73, paragraph after (31): without a contract,
the retailer's unique optimum is below the channel's unique optimum. -/
theorem p73_retailer_bias (M : Model) :
    StrictConvexOn ℝ (Set.Ici 0) M.retailerCost ∧
    ∃ sr so : ℝ, 0 < sr ∧ sr < so ∧
      M.F sr = M.br / (M.hr + M.br) ∧
      M.F so = M.beta / (M.hr + M.beta) ∧
      IsMinOn M.retailerCost Set.univ sr ∧
      IsMinOn M.chainCost Set.univ so ∧
      (∀ s : ℝ, IsMinOn M.retailerCost Set.univ s → s = sr) ∧
      (∀ s : ℝ, IsMinOn M.chainCost Set.univ s → s = so) := by sorry

end CachonCoord.BaseStock

