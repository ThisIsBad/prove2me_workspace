import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (31), p. 73: the unique channel-optimal
base-stock level is positive and satisfies the critical fractile equation. -/
theorem eq_31 (M : Model) :
    ∃ so : ℝ, 0 < so ∧ HasDerivAt M.I (M.F so) so ∧
      M.F so = M.beta / (M.hr + M.beta) ∧
      IsMinOn M.chainCost Set.univ so ∧
      ∀ s : ℝ, IsMinOn M.chainCost Set.univ s → s = so := by sorry

end CachonCoord.BaseStock

