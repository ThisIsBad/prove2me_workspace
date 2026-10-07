import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

open scoped ENNReal

/-- Talagrand (1995), p. 126, Lemma 4.2.1, Eq. (4.2.2): for `α ≥ 0` and `0 < r < 1`,
`inf_{0 ≤ λ ≤ 1} r^{−λα} exp ξ(α, 1 − λ) = 1 + α − α r`.
The infimum is taken in `ℝ≥0∞` (all terms are positive reals). -/
theorem lemma_4_2_1 (α : ℝ) (hα : 0 ≤ α) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (⨅ l ∈ Set.Icc (0 : ℝ) 1, ENNReal.ofReal (r ^ (-(l * α)) * Real.exp (xi α (1 - l))))
      = ENNReal.ofReal (1 + α - α * r) := by sorry

end TalagrandConc.ConvexHull

