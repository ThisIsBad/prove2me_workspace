import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
import Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.FiniteT

/-- Corollary to Theorem 7, p. 802: if `c ≥ 0`, `ε ≥ 0` and
`|c - (d/dt)((1 - F(t))/F′(t))| ≤ ε` for `t ≥ t₀`, then
`|Π_{0,c}(x) - P{(X - t)/a(t) ≤ x | X > t}| ≤ ε` for all `x` and all `t ≥ t₀`. -/
theorem corollary_theorem_7 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' a' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f')
    (ha' : ∀ t ≥ t₀, HasDerivWithinAt (normA μ f) (a' t) (Set.Ici t₀) t)
    (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hclose : ∀ t ≥ t₀, |c - a' t| ≤ ε) :
    ∀ t ≥ t₀, ∀ x : ℝ, |pi0 c x - BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t)| ≤ ε := by sorry

end BalkemaDeHaan.FiniteT

