import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Proof of Proposition 19, p. 877 (Pitman–Yor 1997): identity (52) determines the law of
`V₁` uniquely. Fix `0 ≤ α < 1`. Let `ν₁`, `ν₂` be two families, indexed by `θ > -α`, of
probability measures on `ℝ` carried by `(0, 1)`, each satisfying (52) with its own
`(α, α + θ)` member in the role of the law of `V₁` under `PD(α, α + θ)`:
`ν θ (dx) = Γ(θ+1)/(Γ(θ+α)Γ(1-α)) x^{-α-1}(1-x)^{α+θ-1} ν (α+θ) ((-∞, x/(1-x))) dx` on
`(0, 1)`. Then `ν₁ θ = ν₂ θ` for every `θ > -α`. -/
theorem proposition_19_unique (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
    (ν₁ ν₂ : ℝ → Measure ℝ)
    (h₁ : ∀ θ : ℝ, -α < θ →
      IsProbabilityMeasure (ν₁ θ) ∧ ν₁ θ (Set.Ioo (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo (0 : ℝ) 1 →
          ν₁ θ s = ∫⁻ x in s, ENNReal.ofReal
            (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
              * x ^ (-α - 1) * (1 - x) ^ (α + θ - 1)
              * (ν₁ (α + θ) (Set.Iio (x / (1 - x)))).toReal))
    (h₂ : ∀ θ : ℝ, -α < θ →
      IsProbabilityMeasure (ν₂ θ) ∧ ν₂ θ (Set.Ioo (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo (0 : ℝ) 1 →
          ν₂ θ s = ∫⁻ x in s, ENNReal.ofReal
            (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
              * x ^ (-α - 1) * (1 - x) ^ (α + θ - 1)
              * (ν₂ (α + θ) (Set.Iio (x / (1 - x)))).toReal)) :
    ∀ θ : ℝ, -α < θ → ν₁ θ = ν₂ θ := by sorry

end PoissonDirichlet.MaxDensity

