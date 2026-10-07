import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
import Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.FiniteT

/-- The exponential representation, proof of Theorem 7, p. 802: for `t ≥ t₀` and `x ≥ 0`,
`P{(X - t)/a(t) > x | X > t} = (1 - F(t + x a(t)))/(1 - F(t))
= exp(-∫₀ˣ a(t)/a(t + s a(t)) ds)`. -/
theorem exp_representation (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f') :
    ∀ t ≥ t₀, ∀ x : ℝ, 0 ≤ x →
      1 - BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t)
          = (1 - cdf μ (t + x * normA μ f t)) / (1 - cdf μ t) ∧
        (1 - cdf μ (t + x * normA μ f t)) / (1 - cdf μ t)
          = Real.exp (-∫ s in (0 : ℝ)..x, normA μ f t / normA μ f (t + s * normA μ f t)) := by sorry

end BalkemaDeHaan.FiniteT

