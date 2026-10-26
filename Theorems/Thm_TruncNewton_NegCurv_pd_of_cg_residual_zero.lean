import Mathlib
import Definitions.Def_TruncNewton_NegCurv_Setting

namespace TruncNewton.NegCurv

theorem pd_of_cg_residual_zero {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (g : EuclideanSpace ℝ (Fin n))
    (hg : ∀ μ : ℝ, (∃ v, v ≠ 0 ∧ H v = μ • v) → ∃ v, H v = μ • v ∧ inner ℝ g v ≠ 0)
    (i : ℕ) (hcurv : ∀ j ≤ i, 0 < inner ℝ ((cg H g j).d) (H (cg H g j).d))
    (hr : (cg H g (i + 1)).r = 0) :
    ∀ v, v ≠ 0 → 0 < inner ℝ v (H v) := by sorry

end TruncNewton.NegCurv

