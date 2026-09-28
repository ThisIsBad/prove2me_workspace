import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.ConvexRates

/-- Theorem 3.1: if `f` is `L`-Lipschitz on the closed ball `B(x*, (1 + γ/β)‖z⁰ - z*‖)`,
`x* = prox_{γg}(z*)`, then `(f+g+h)(x^k_g) - (f+g+h)(x*) = o(1/√(k+1))`: the objective values are
finite and `√(k+1) ((f+g+h)(x^k_g) - (f+g+h)(x*)) → 0`. -/
theorem last_iterate_rate
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
      (∀ k : ℕ, objective f g h (algXg proxf proxg (gradient h) γ z0 k) ≠ ⊤) ∧
      Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) + 1) *
          ((objective f g h (algXg proxf proxg (gradient h) γ z0 k)).toReal - (objective f g h (proxg zstar)).toReal))
        atTop (𝓝 0) := by sorry

end ThreeOpSplitting.ConvexRates

