import Mathlib
import Definitions.Def_TalagrandConc_TwoPoint_Basic

open MeasureTheory
open scoped ENNReal NNReal

namespace TalagrandConc.TwoPoint

/-- Talagrand (1995), Lemma 2.3.5, Eq. (2.3.8), p. 90. Standing assumptions of §2.3:
`μ({1}) = p`, `μ₁({1}) = p₁ > p`; `t ≥ 0` and `α > 0` as in Theorem 2.3.4.
The numbers `a ≤ b ≤ 1` are taken in `ℝ≥0∞` so that `a = 0` (used in the proof of
Theorem 2.3.4 for `N = 1`) is allowed, with `1 / 0^α = ∞`. -/
theorem lemma_2_3_5 (p p₁ : unitInterval) (hpp₁ : p < p₁)
    (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) (a b : ℝ≥0∞) (hab : a ≤ b) (hb : b ≤ 1) :
    ENNReal.ofReal (1 - (p : ℝ)) / b ^ α
        + ENNReal.ofReal (p : ℝ) * min (1 / a ^ α) (ENNReal.ofReal (Real.exp t) / b ^ α)
      ≤ ENNReal.ofReal (aConst α t (p : ℝ) (p₁ : ℝ))
          / (a * ENNReal.ofReal (p₁ : ℝ) + b * ENNReal.ofReal (1 - (p₁ : ℝ))) ^ α := by sorry

end TalagrandConc.TwoPoint

