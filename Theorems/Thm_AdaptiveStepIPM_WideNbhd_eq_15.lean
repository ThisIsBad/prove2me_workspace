import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- Inequality (15) in the proof of Theorem 2 of Mizuno–Todd–Ye (p. 10): for `β, γ ∈ (0, 1)` with
`γ ≤ 2(1 − β)` and `N = N_∞(β)` or `N_∞⁻(β)`, one iteration `(x, s) ↦ (x⁺, s⁺)` of Algorithm 2
satisfies `μ⁺ ≤ (1 − 4βγ(1 − γ)/n) μ`, where `μ = xᵀs/n`, `μ⁺ = (x⁺)ᵀs⁺/n`. -/
theorem eq_15 {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (N : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (hN : N = Ninf A b c β ∨ N = NinfMinus A b c β) (x s x' s' : Fin n → ℝ)
    (hstep : Alg2Step A N γ x s x' s') :
    AdaptiveStepIPM.PredCorr.mu x' s' ≤ (1 - 4 * β * γ * (1 - γ) / n) * AdaptiveStepIPM.PredCorr.mu x s := by sorry

end AdaptiveStepIPM.WideNbhd

