import Mathlib
import Definitions.Def_StochLinOpt_LowerBound_circleBandit

open Matrix

namespace StochLinOpt.LowerBound

theorem bias_increment_le (μ₁ μ₂ x : Fin 2 → ℝ) (p ℓ : ℝ)
    (hμ₁ : μ₁ ⬝ᵥ μ₁ = 1 / 4) (hμ₂ : μ₂ ⬝ᵥ μ₂ = 1 / 4) (hx : x ∈ unitCircle)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hℓ : ℓ = 1 ∨ ℓ = -1) :
    |biasUpdate μ₁ μ₂ x p ℓ - (2 * p - 1)| ≤ |(μ₁ - μ₂) ⬝ᵥ x| := by sorry

end StochLinOpt.LowerBound
