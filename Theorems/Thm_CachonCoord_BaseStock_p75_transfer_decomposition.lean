import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, p. 75: for any constant rates `t_I`, `t_B` (positive meaning a
payment from the supplier to the retailer) and any inventory level `y`,
`t_I I_r(y) + t_B B_r(y) = (t_I + t_B) I_r(y) + t_B (μ_r - y)`. -/
theorem p75_transfer_decomposition (M : Model) :
    ∀ tI tB y : ℝ,
      tI * M.I y + tB * M.B y = (tI + tB) * M.I y + tB * (M.meanDemand - y) := by sorry

end CachonCoord.BaseStock

