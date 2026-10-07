import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (28), p. 72: expected on-hand inventory is the
integral of the lead-time demand distribution function. -/
theorem eq_28 (M : Model) :
    ∀ y : ℝ, 0 ≤ y →
      M.I y = ∫ x in (0 : ℝ)..y, (y - x) * M.density x ∧
      M.I y = ∫ x in (0 : ℝ)..y, M.F x := by sorry

end CachonCoord.BaseStock

