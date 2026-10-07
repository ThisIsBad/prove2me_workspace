import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_ResidualLife
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.ParetoBounds

/-- Theorem 6, p. 801 (Balkema–de Haan 1974): if `F = cdf μ` has a positive density `f`
on `[t₀, ∞)` with `α₁ ≤ t f(t)/(1 - F(t)) ≤ α₂` for `t ≥ t₀`, then for every `t ≥ t₀`
and every real `x`,
`Γ_{α₁}(x) ≤ P{(X - t)/t ≤ x | X > t} ≤ Γ_{α₂}(x)`, where
`P{(X - t)/t ≤ x | X > t} = F_t(x t)`. -/
theorem theorem_6 (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂) :
    ∀ t ≥ t₀, ∀ x : ℝ,
      GammaLaw α₁ x ≤ residualLife μ t (x * t) ∧ residualLife μ t (x * t) ≤ GammaLaw α₂ x := by sorry

end BalkemaDeHaan.ParetoBounds

