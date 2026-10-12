import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 3.2, (3.2), p. 537: for `0 < λ ≤ w` and `w ≥ 1`,
`(w − 1)! λ^{−w} Σ_{k=w}^∞ λ^k/k! ≤ 2w^{−1/2}`. -/
theorem lemma_3_2 (lam : ℝ) (hlam : 0 < lam) (w : ℕ) (hw : 1 ≤ w) (hlw : lam ≤ w) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ)
      ≤ 2 / Real.sqrt w := by sorry

end PoissonDepTrials.SecondOrder

