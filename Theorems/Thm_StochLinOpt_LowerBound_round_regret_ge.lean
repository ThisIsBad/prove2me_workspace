import Mathlib
import Definitions.Def_StochLinOpt_LowerBound_circleBandit

open Matrix

namespace StochLinOpt.LowerBound

theorem round_regret_ge (μ₁ μ₂ x : Fin 2 → ℝ) (ε p ℓ : ℝ)
    (hμ₁ : μ₁ ⬝ᵥ μ₁ = 1 / 4) (hμ₂ : μ₂ ⬝ᵥ μ₂ = 1 / 4)
    (hε : 0 < ε) (hdist : (μ₁ - μ₂) ⬝ᵥ (μ₁ - μ₂) = ε ^ 2) (hx : x ∈ unitCircle)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hℓ : ℓ = 1 ∨ ℓ = -1) :
    1 / 16 * (ε ^ 2 + (biasUpdate μ₁ μ₂ x p ℓ - (2 * p - 1)) ^ 2 / ε ^ 2) *
        (if |2 * p - 1| ≤ 1 / 2 then 1 else 0) ≤
      p * (μ₁ ⬝ᵥ x - optCost μ₁) + (1 - p) * (μ₂ ⬝ᵥ x - optCost μ₂) := by sorry

end StochLinOpt.LowerBound
