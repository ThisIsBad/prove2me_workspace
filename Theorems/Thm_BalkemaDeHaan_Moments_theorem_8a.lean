import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw
import Definitions.Def_BalkemaDeHaan_Moments_ResidualLife

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.Moments

/-- Theorem 8(a), p. 803, **corrected**: suppose `F(x) < 1` for all real `x` and `0 < ξ < α`. Then
`lim_{t→∞} P{X/t ≤ x | X > t} = Γ_α(x − 1)` for all `x > 0` if and only if `∫_0^∞ y^ξ dF(y)` is
finite and `lim_{t→∞} E((X/t)^ξ | X > t) = (1 − ξ/α)^{−1}`. (The page's right-hand side asks only that
the limit exist and be finite, which does not determine `α`; see the Formalization Note.) -/
theorem theorem_8a (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α) :
    (∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => scaledResidualCDF μ t x) atTop (𝓝 (BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)))) ↔
    (IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ ∧
      Tendsto (fun t : ℝ => condMoment μ ξ t) atTop (𝓝 (1 - ξ / α)⁻¹)) := by sorry

end BalkemaDeHaan.Moments

