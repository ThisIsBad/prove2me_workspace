import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
import Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.FiniteT

/-- The bounds (13), proof of Theorem 7, p. 802: if `c₁ ≤ a′ ≤ c₂` on `[t₀, ∞)` for
`a(t) = (1 - F(t))/F′(t)`, then for `t ≥ t₀` and `x ≥ 0`,
`c₁ x a(t) ≤ a(t + x a(t)) - a(t) ≤ c₂ x a(t)` and `1 + c₁ x ≤ a(t + x a(t))/a(t) ≤ 1 + c₂ x`. -/
theorem bounds_13 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' a' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f')
    (ha' : ∀ t ≥ t₀, HasDerivWithinAt (normA μ f) (a' t) (Set.Ici t₀) t)
    (c₁ c₂ : ℝ) (hc : ∀ t ≥ t₀, c₁ ≤ a' t ∧ a' t ≤ c₂) :
    ∀ t ≥ t₀, ∀ x : ℝ, 0 ≤ x →
      (c₁ * x * normA μ f t ≤ normA μ f (t + x * normA μ f t) - normA μ f t ∧
        normA μ f (t + x * normA μ f t) - normA μ f t ≤ c₂ * x * normA μ f t) ∧
      (1 + c₁ * x ≤ normA μ f (t + x * normA μ f t) / normA μ f t ∧
        normA μ f (t + x * normA μ f t) / normA μ f t ≤ 1 + c₂ * x) := by sorry

end BalkemaDeHaan.FiniteT

