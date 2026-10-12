import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 3.3, (3.3), p. 537: `‖S_λh‖ ≤ 4‖h‖ min(λ^{−1/2}, 1)`, the norm of `S_λh` taken over
its domain `w ≥ 1` and `‖h‖` replaced by any bound `M` on `|h|`. -/
theorem lemma_3_3 (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein lam h w| ≤ 4 * M * min (1 / Real.sqrt lam) 1 := by sorry

end PoissonDepTrials.SecondOrder

