import Mathlib

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.ParetoBounds

/-- Proof of Theorem 6, p. 801 (Balkema–de Haan 1974): integrating the hazard bounds
`α₁ ≤ t F'(t)/(1 - F(t)) ≤ α₂` between `t` and `(1 + x) t`, `x > 0`, gives
`α₁ ∫ du/u ≤ ∫ F'(u)/(1 - F(u)) du ≤ α₂ ∫ du/u`. The density `F' = f` is a (right,
at `t₀`) derivative of `F = cdf μ` on `[t₀, ∞)`. -/
theorem integration_display (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂)
    (t : ℝ) (ht : t₀ ≤ t) (x : ℝ) (hx : 0 < x) :
    α₁ * ∫ u in t..(1 + x) * t, 1 / u ≤ ∫ u in t..(1 + x) * t, f u / (1 - cdf μ u) ∧
      ∫ u in t..(1 + x) * t, f u / (1 - cdf μ u) ≤ α₂ * ∫ u in t..(1 + x) * t, 1 / u := by sorry

end BalkemaDeHaan.ParetoBounds

