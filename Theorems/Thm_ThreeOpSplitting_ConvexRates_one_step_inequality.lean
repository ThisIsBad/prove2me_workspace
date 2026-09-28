import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.ConvexRates

/-- Eq. (3.2): for all `k ≥ 0`, with `x* = prox_{γg}(z*)`,
`2γ(f(x^k_f) + g(x^k_g) + h(x^k_g) - (f+g+h)(x*)) ≤ ‖z^k - x*‖² - ‖z^{k+1} - x*‖²
  - ‖z^k - z^{k+1}‖² + 2γ⟪z^k - z^{k+1}, ∇h(x^k_g)⟫`. -/
theorem one_step_inequality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar) :
    ∀ k : ℕ,
      ((2 * γ : ℝ) : EReal) *
          (f (algXf proxf proxg (gradient h) γ z0 k) + g (algXg proxf proxg (gradient h) γ z0 k) + ((h (algXg proxf proxg (gradient h) γ z0 k) : ℝ) : EReal)
            - objective f g h (proxg zstar)) ≤
        ((‖algZ proxf proxg (gradient h) γ z0 k - proxg zstar‖ ^ 2 - ‖algZ proxf proxg (gradient h) γ z0 (k + 1) - proxg zstar‖ ^ 2
            - ‖algZ proxf proxg (gradient h) γ z0 k - algZ proxf proxg (gradient h) γ z0 (k + 1)‖ ^ 2
            + 2 * γ * ⟪algZ proxf proxg (gradient h) γ z0 k - algZ proxf proxg (gradient h) γ z0 (k + 1), gradient h (algXg proxf proxg (gradient h) γ z0 k)⟫_ℝ : ℝ) : EReal) := by sorry

end ThreeOpSplitting.ConvexRates

