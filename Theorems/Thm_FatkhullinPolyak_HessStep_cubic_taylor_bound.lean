import Mathlib
import Definitions.Def_FatkhullinPolyak_HessStep_hessianStepMethod

namespace FatkhullinPolyak.HessStep

theorem cubic_taylor_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hM : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ M * ‖x - y‖) :
    ∀ x y : EuclideanSpace ℝ (Fin n),
      |f (x + y) - f x - inner ℝ (gradient f x) y - (1 / 2) * hessQuad f x y| ≤ M / 6 * ‖y‖ ^ 3 := by sorry

end FatkhullinPolyak.HessStep
