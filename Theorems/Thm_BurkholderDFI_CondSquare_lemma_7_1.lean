import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.CondSquare

/-- Lemma 7.1, p. 26: a good-λ inequality `P(g > βλ, f ≤ δλ) ≤ εP(g > λ)`, together with
`Φ(βλ) ≤ γΦ(λ)`, `Φ(δ⁻¹λ) ≤ ηΦ(λ)` and `γε < 1`, gives `EΦ(g) ≤ γη/(1 − γε) · EΦ(f)`. -/
theorem lemma_7_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (β δ ε : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hε : 0 < ε)
    (h71 : ∀ l : ℝ, 0 < l →
      P {ω | ENNReal.ofReal (β * l) < g ω ∧ f ω ≤ ENNReal.ofReal (δ * l)}
        ≤ ENNReal.ofReal ε * P {ω | ENNReal.ofReal l < g ω})
    (γ η : ℝ≥0)
    (h72 : ∀ l : ℝ, 0 < l →
      Φ (ENNReal.ofReal (β * l)) ≤ γ * Φ (ENNReal.ofReal l) ∧
      Φ (ENNReal.ofReal (δ⁻¹ * l)) ≤ η * Φ (ENNReal.ofReal l))
    (hγε : (γ : ℝ) * ε < 1) :
    ∫⁻ ω, Φ (g ω) ∂P ≤ ENNReal.ofReal (γ * η / (1 - γ * ε)) * ∫⁻ ω, Φ (f ω) ∂P := by sorry

end BurkholderDFI.CondSquare

