import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

open scoped ENNReal

/-- Talagrand (1995), p. 124, Lemma 4.1.3, Eq. (4.1.6): for `0 ≤ r ≤ 1`,
`inf_{0 ≤ λ ≤ 1} r^{−λ} exp((1 − λ)²/4) ≤ 2 − r`.
Computed in `ℝ≥0∞`, so that `0^{−λ} = +∞` for `λ > 0` and `0^0 = 1`. -/
theorem lemma_4_1_3 (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (⨅ l ∈ Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal r ^ (-l) * ENNReal.ofReal (Real.exp ((1 - l) ^ 2 / 4)))
      ≤ ENNReal.ofReal (2 - r) := by sorry

end TalagrandConc.ConvexHull

