import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem smoothing_gradient_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    Differentiable ℝ (RandomGradFree.Shared.smoothing f μ) ∧
      ∀ x y, ‖gradient (RandomGradFree.Shared.smoothing f μ) x - gradient (RandomGradFree.Shared.smoothing f μ) y‖ ≤ L₁ * ‖x - y‖ := by sorry

end RandomGradFree.Accelerated
