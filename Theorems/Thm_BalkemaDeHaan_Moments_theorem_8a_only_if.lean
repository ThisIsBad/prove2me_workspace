import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw
import Definitions.Def_BalkemaDeHaan_Moments_ResidualLife

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.Moments

/-- Theorem 8(a), p. 803, the "only if" half together with "Then c = (1 − ξ/α)^{−1}": if
`F(x) < 1` for all `x`, `0 < ξ < α` and `P{X/t ≤ x | X > t} → Γ_α(x − 1)` as `t → ∞` for all
`x > 0`, then `∫_0^∞ y^ξ dF(y)` is finite and `E((X/t)^ξ | X > t) → (1 − ξ/α)^{−1}`. -/
theorem theorem_8a_only_if (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α)
    (hlim : ∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => scaledResidualCDF μ t x) atTop (𝓝 (BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)))) :
    IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ ∧
    Tendsto (fun t : ℝ => condMoment μ ξ t) atTop (𝓝 (1 - ξ / α)⁻¹) := by sorry

end BalkemaDeHaan.Moments

