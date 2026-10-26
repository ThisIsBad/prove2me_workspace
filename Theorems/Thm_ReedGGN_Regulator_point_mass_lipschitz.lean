import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Proposition 3.1, p. 32, (A.2): when `B` is concentrated on `c > 0`, for càdlàg
solutions `z₁, z₂` of (3.1) with càdlàg inputs `x₁, x₂`: `‖z₁ − z₂‖_t = ‖x₁ − x₂‖_t` for
`0 ≤ t < c`, and for every integer `k ≥ 1` and every `(k − 1)c ≤ t < kc`,
`‖z₁ − z₂‖_t ≤ k ‖x₁ − x₂‖_t`. -/
theorem point_mass_lipschitz (c a : ℝ) (hc : 0 < c) (x₁ x₂ z₁ z₂ : ℝ → ℝ)
    (hx₁ : IsCadlag x₁) (hx₂ : IsCadlag x₂) (hz₁ : IsCadlag z₁) (hz₂ : IsCadlag z₂)
    (h₁ : SolvesRegulator (Measure.dirac c) a x₁ z₁)
    (h₂ : SolvesRegulator (Measure.dirac c) a x₂ z₂) :
    (∀ t : ℝ, 0 ≤ t → t < c → supNorm t (z₁ - z₂) = supNorm t (x₁ - x₂)) ∧
    ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, ((k : ℝ) - 1) * c ≤ t → t < k * c →
      supNorm t (z₁ - z₂) ≤ k * supNorm t (x₁ - x₂) := by sorry

end ReedGGN.Regulator

