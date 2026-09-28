import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.ConvexRates

/-- Eq. (2.7) for Algorithm 2 with `λ_k ≡ 1`: for every `ε ∈ (γ/(2β), 1)` the squared gradient
differences `‖∇h(x^i_g) - ∇h(x*)‖²`, `x* = prox_{γg}(z*)`, are summable and their tail from `k` is at
most `‖z^k - z*‖² / (γ(2β - γ/ε))`. -/
theorem gradient_tail_sum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar)
    (ε : ℝ) (hε₁ : γ / (2 * β) < ε) (hε₂ : ε < 1) :
    Summable (fun i : ℕ => ‖gradient h (algXg proxf proxg (gradient h) γ z0 i) - gradient h (proxg zstar)‖ ^ 2) ∧
      ∀ k : ℕ, ∑' i : ℕ, ‖gradient h (algXg proxf proxg (gradient h) γ z0 (i + k)) - gradient h (proxg zstar)‖ ^ 2 ≤
        ‖algZ proxf proxg (gradient h) γ z0 k - zstar‖ ^ 2 / (γ * (2 * β - γ / ε)) := by sorry

end ThreeOpSplitting.ConvexRates

