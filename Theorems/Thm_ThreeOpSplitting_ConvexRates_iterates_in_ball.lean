import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.ConvexRates

/-- Lemma 3.1 for Algorithm 2 with `λ_k ≡ 1`: with `x* = prox_{γg}(z*)`, every `x^j_f` and every
`x^j_g` lies in the closed ball of centre `x*` and radius `(1 + γ/β)‖z⁰ - z*‖`. -/
theorem iterates_in_ball
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar) :
    ∀ j : ℕ, algXf proxf proxg (gradient h) γ z0 j ∈ Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖) ∧
      algXg proxf proxg (gradient h) γ z0 j ∈ Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖) := by sorry

end ThreeOpSplitting.ConvexRates

