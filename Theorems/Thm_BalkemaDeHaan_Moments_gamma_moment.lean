import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.Moments

/-- Theorem 8(a), p. 803, "Then c = ∫_0^∞ x^ξ dΓ_α(x − 1) = (1 − ξ/α)^{−1}": for `0 < ξ < α`,
there is a probability law on `ℝ` whose distribution function is `x ↦ Γ_α(x − 1)`, and every such
law `ν` has a finite `ξ`-th moment on `(0, ∞)` equal to `(1 − ξ/α)^{−1}`. -/
theorem gamma_moment (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α) :
    (∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)) ∧
    ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)) →
      IntegrableOn (fun x : ℝ => x ^ ξ) (Set.Ioi 0) ν ∧
      ∫ x in Set.Ioi 0, x ^ ξ ∂ν = (1 - ξ / α)⁻¹ := by sorry

end BalkemaDeHaan.Moments

