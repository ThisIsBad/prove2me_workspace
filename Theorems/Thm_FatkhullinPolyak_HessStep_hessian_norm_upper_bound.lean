import Mathlib
import Definitions.Def_FatkhullinPolyak_HessStep_hessianStepMethod

namespace FatkhullinPolyak.HessStep

theorem hessian_norm_upper_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hconv : StrongConvexOn Set.univ μ f)
    (hL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x) + L / (2 * μ) * hessQuad f x (y - x) := by sorry

end FatkhullinPolyak.HessStep
