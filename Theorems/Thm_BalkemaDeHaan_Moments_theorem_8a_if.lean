import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw
import Definitions.Def_BalkemaDeHaan_Moments_ResidualLife

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.Moments

/-- Theorem 8(a), p. 803, the "if" half, **corrected**: if `F(x) < 1` for all `x`, `0 < ξ < α`,
`∫_0^∞ y^ξ dF(y)` is finite and `E((X/t)^ξ | X > t) → (1 − ξ/α)^{−1}` as `t → ∞`, then
`P{X/t ≤ x | X > t} → Γ_α(x − 1)` for all `x > 0`. The page asks only that the limit `c` exist and be
finite; that is false (a Pareto BalkemaDeHaan.LimitTypes.tail `x^{−β}`, `β > ξ`, `β ≠ α`, gives `c = (1 − ξ/β)^{−1}` and the
limit law `Γ_β(x − 1)`), so the limit value `(1 − ξ/α)^{−1}` is part of the hypothesis. -/
theorem theorem_8a_if (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α)
    (hmom : IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ)
    (hc : Tendsto (fun t : ℝ => condMoment μ ξ t) atTop (𝓝 (1 - ξ / α)⁻¹)) :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => scaledResidualCDF μ t x) atTop (𝓝 (BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1))) := by sorry

end BalkemaDeHaan.Moments

