import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Proposition 3.1, Lipschitz continuity (p. 34): under the window condition of the
non-degenerate case, for càdlàg solutions `z₁, z₂` of (3.1) with càdlàg inputs `x₁, x₂` and
every integer `k ≥ 1`, `‖z₂ − z₁‖_{kδ} ≤ (1 − ε)^{−k} ‖x₂ − x₁‖_{kδ}`. -/
theorem lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ] (a δ ε : ℝ)
    (hδ : 0 < δ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hB₀ : μ (Set.Icc 0 δ) < ENNReal.ofReal ε)
    (hB : ∀ y, 0 ≤ y → μ (Set.Ioc y (y + δ)) < ENNReal.ofReal ε)
    (x₁ x₂ z₁ z₂ : ℝ → ℝ)
    (hx₁ : IsCadlag x₁) (hx₂ : IsCadlag x₂) (hz₁ : IsCadlag z₁) (hz₂ : IsCadlag z₂)
    (h₁ : SolvesRegulator μ a x₁ z₁) (h₂ : SolvesRegulator μ a x₂ z₂) :
    ∀ k : ℕ, 1 ≤ k →
      supNorm (k * δ) (z₂ - z₁) ≤ (1 - ε)⁻¹ ^ k * supNorm (k * δ) (x₂ - x₁) := by sorry

end ReedGGN.Regulator

