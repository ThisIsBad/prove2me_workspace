import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 3.5, (3.5), p. 537: for `w ≥ 1`,
`|ΔS_λh(w)| ≤ λ^{−1}‖h‖{2 + 4|w − λ| min(λ^{−1/2}, 1)}`. -/
theorem lemma_3_5 (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |delta (stein lam h) w| ≤
      lam⁻¹ * M * (2 + 4 * |(w : ℝ) - lam| * min (1 / Real.sqrt lam) 1) := by sorry

end PoissonDepTrials.SecondOrder

