import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (30) and following sentence, p. 73:
the channel cost formula and strict convexity for feasible nonnegative stock levels. -/
theorem eq_30 (M : Model) :
    (∀ s : ℝ, M.chainCost s =
      M.beta * (M.meanDemand - s) + (M.hr + M.beta) * M.I s) ∧
    StrictConvexOn ℝ (Set.Ici 0) M.chainCost := by sorry

end CachonCoord.BaseStock

