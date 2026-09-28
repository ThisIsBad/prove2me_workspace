import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.ConvexRates

/-- Eq. (3.4): the weighted ergodic iterates of `(x^i_f)` and `(x^i_g)` satisfy
`‖x̄^k_f - x̄^k_g‖ ≤ 5‖z⁰ - z*‖ / (k + 1)` for all `k ≥ 0`. -/
theorem weighted_ergodic_distance
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar) :
    ∀ k : ℕ, ‖weightedErgodic (algXf proxf proxg (gradient h) γ z0) k - weightedErgodic (algXg proxf proxg (gradient h) γ z0) k‖ ≤
      5 * ‖z0 - zstar‖ / ((k : ℝ) + 1) := by sorry

end ThreeOpSplitting.ConvexRates

