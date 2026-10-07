import Mathlib
import Definitions.Def_BalkemaDeHaan_Moments_ResidualLife

open MeasureTheory

namespace BalkemaDeHaan.Moments

/-- Proof of Theorem 8(a), p. 803, the displayed identity: if `∫_0^∞ y^ξ dF(y) < ∞` (`ξ > 0`) and
`F(x) < 1` for all `x`, then for every `x > 0` the function `y ↦ y^{ξ−1}(1 − F(y))` is Lebesgue
integrable on `(x, ∞)`, the left side of the display is `E((X/x)^ξ | X > x)`, and
`∫_x^∞ y^ξ dF(y) / (x^ξ(1 − F(x))) = ξ ∫_x^∞ y^{ξ−1}(1 − F(y)) dy / (x^ξ(1 − F(x))) + 1`. -/
theorem tail_moment_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (ξ : ℝ) (hξ : 0 < ξ)
    (hmom : IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ)
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => y ^ (ξ - 1) * BalkemaDeHaan.LimitTypes.tail μ y) (Set.Ioi x) ∧
    condMoment μ ξ x = (∫ y in Set.Ioi x, y ^ ξ ∂μ) / (x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x) ∧
    (∫ y in Set.Ioi x, y ^ ξ ∂μ) / (x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x) =
      ξ * (∫ y in Set.Ioi x, y ^ (ξ - 1) * BalkemaDeHaan.LimitTypes.tail μ y) / (x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x) + 1 := by sorry

end BalkemaDeHaan.Moments

