import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

/-- Lemma 3.8: under the standing assumptions of §3.4, for every model point `x_k` and every
`x`, `‖Gf(x) - G_{f̂_k}(x)‖ ≤ (L2/2) ‖x - x_k‖²`, where `f̂_k = ĝ_k + h` is the model with the
exact Hessian `∇²g(x_k)`. -/
theorem compGradStep_model_approx {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (m L1 L2 : ℝ)
    (hg : SmoothPartAssumptions g m L1 L2) (hh : IsProperClosedConvex D h)
    (xk x : EuclideanSpace ℝ (Fin n)) :
    ‖compGradStep g D h 1 x - compGradStep (quadModel g xk) D h 1 x‖ ≤
      L2 / 2 * ‖x - xk‖ ^ 2 := by sorry

end ProxNewton.Inexact
