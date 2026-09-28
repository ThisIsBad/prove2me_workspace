import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.ConvexRates

/-- Theorem 3.2: if `f` is `L`-Lipschitz on the closed ball `B(x*, (1 + γ/β)‖z⁰ - z*‖)`,
`x* = prox_{γg}(z*)`, then at the weighted ergodic iterate
`x̄^k_g = 2/((k+1)(k+2)) ∑_{i=0}^k (i+1) x^i_g` the objective error is `O(1/(k+1))`: there is a
constant `C` (depending on the data but not on `k`) with
`(f+g+h)(x̄^k_g) ≤ (f+g+h)(x*) + C/(k+1)` for all `k ≥ 0`, and `(f+g+h)(x*)` is finite. -/
theorem weighted_ergodic_rate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar)
    (L : NNReal)
    (hfin : ∀ x ∈ Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖), f x ≠ ⊤)
    (hLip : LipschitzOnWith L (fun x => (f x).toReal)
      (Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖))) :
    objective f g h (proxg zstar) ≠ ⊤ ∧
      ∃ C : ℝ, ∀ k : ℕ,
        objective f g h (weightedErgodic (algXg proxf proxg (gradient h) γ z0) k) ≤
          objective f g h (proxg zstar) + ((C / ((k : ℝ) + 1) : ℝ) : EReal) := by sorry

end ThreeOpSplitting.ConvexRates

