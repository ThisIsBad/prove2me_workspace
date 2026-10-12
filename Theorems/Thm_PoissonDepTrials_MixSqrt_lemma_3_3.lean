import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 3.3, p. 537, (3.3): `‖S_λh‖ ≤ 4‖h‖ min(λ^{−1/2}, 1)`, with `‖h‖` given
as any bound `M` on `|h|` and `‖S_λh‖` the supremum over `w ≥ 1`. -/
theorem lemma_3_3 (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein lam h w| ≤ 4 * M * min (1 / Real.sqrt lam) 1 := by sorry

end PoissonDepTrials.MixSqrt

