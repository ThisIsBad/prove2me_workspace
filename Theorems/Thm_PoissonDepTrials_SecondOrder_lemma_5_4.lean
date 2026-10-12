import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 5.4, (5.4), p. 543: for `w ≥ 1`,
`|S_bU_λh(w)| ≤ 4λ^{−1}‖h‖[(2 + 4|1 + b − λ|) min(b^{−1/2}, 1) + 3 min(λ^{−1/2}, 1)]`. -/
theorem lemma_5_4 (lam : ℝ) (hlam : 0 < lam) (b : ℝ) (hb : 0 < b) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein b (stU lam h) w| ≤
      4 * lam⁻¹ * M * ((2 + 4 * |1 + b - lam|) * min (1 / Real.sqrt b) 1 +
        3 * min (1 / Real.sqrt lam) 1) := by sorry

end PoissonDepTrials.SecondOrder

