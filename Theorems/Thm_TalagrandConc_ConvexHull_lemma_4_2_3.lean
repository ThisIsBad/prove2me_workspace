import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

/-- Talagrand (1995), p. 127, Lemma 4.2.3: for `α, a > 0`,
`1 + α − α a ≤ a^{−α}` (Eq. (4.2.3)) and `a + (1 − a) exp ξ(α, 1) ≤ a^{−α}` (Eq. (4.2.4)). -/
theorem lemma_4_2_3 (α a : ℝ) (hα : 0 < α) (ha : 0 < a) :
    1 + α - α * a ≤ a ^ (-α) ∧ a + (1 - a) * Real.exp (xi α 1) ≤ a ^ (-α) := by sorry

end TalagrandConc.ConvexHull

