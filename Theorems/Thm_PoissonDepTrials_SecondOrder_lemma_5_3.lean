import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 5.3, (5.3), p. 543: for `m = 0, 1, 2, …`,
`𝒫_b|L^m U_λh| ≤ 2λ^{−1}‖h‖[1 + 2|m + 1 + b − λ| + 2b^{1/2} min(λ^{−1/2}, 1)]`,
with `L^m U_λh(w) = U_λh(w + m)`. -/
theorem lemma_5_3 (lam : ℝ) (hlam : 0 < lam) (b : ℝ) (hb : 0 < b) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) (m : ℕ) :
    poissonExp b (fun w => |stU lam h (w + m)|) ≤
      2 * lam⁻¹ * M * (1 + 2 * |(m : ℝ) + 1 + b - lam| + 2 * Real.sqrt b * min (1 / Real.sqrt lam) 1) := by sorry

end PoissonDepTrials.SecondOrder

