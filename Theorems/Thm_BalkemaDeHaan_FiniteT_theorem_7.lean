import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
import Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.FiniteT

/-- Theorem 7, pp. 801–802: let `F = cdf μ` have a positive, differentiable density `f` for
`t ≥ t₀`, and let `c₁ ≤ (d/dt)((1 - F(t))/F′(t)) ≤ c₂` for `t ≥ t₀`. Then for `t ≥ t₀`
and all `x`, `Π_{0,c₂}(x) ≤ P{(X - t)/a(t) ≤ x | X > t} ≤ Π_{0,c₁}(x)`, where
`a(t) = (1 - F(t))/F′(t)` and `P{(X - t)/a(t) ≤ x | X > t} = F_t(x a(t))`. -/
theorem theorem_7 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' a' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f')
    (ha' : ∀ t ≥ t₀, HasDerivWithinAt (normA μ f) (a' t) (Set.Ici t₀) t)
    (c₁ c₂ : ℝ) (hc : ∀ t ≥ t₀, c₁ ≤ a' t ∧ a' t ≤ c₂) :
    ∀ t ≥ t₀, ∀ x : ℝ,
      pi0 c₂ x ≤ BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t) ∧
        BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t) ≤ pi0 c₁ x := by sorry

end BalkemaDeHaan.FiniteT

