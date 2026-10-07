import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (29), p. 72: the expected backorders
equal mean demand minus the stock level plus expected inventory. -/
theorem eq_29 (M : Model) :
    ∀ y : ℝ, M.B y = M.meanDemand - y + M.I y := by sorry

end CachonCoord.BaseStock

