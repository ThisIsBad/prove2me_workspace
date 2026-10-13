import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- Proof of Theorem 2 of Mizuno–Todd–Ye (p. 10): for `β, γ ∈ (0, 1)` with `γ ≤ 2(1 − β)`,
`(x, s) ∈ N_∞⁻(β)` and a solution `d` of (2) at `(x, s)` with `γ`,
`‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞ ≤ ‖AdaptiveStepIPM.PredCorr.Pq‖_∞ ≤ ‖r‖²/4 ≤ nμ/4`, hence `θ₂⁻ ≥ θ₂ ≥ 4βγ/n`. The last step needs `n ≥ 2`. -/
theorem theta2_lower_bound {n m : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hγβ : γ ≤ 2 * (1 - β)) (x s : Fin n → ℝ) (hN : (x, s) ∈ NinfMinus A b c β)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds) :
    normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ∧
      normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ norm2 (rvec γ x s) ^ 2 / 4 ∧
      norm2 (rvec γ x s) ^ 2 / 4 ≤ (n : ℝ) * AdaptiveStepIPM.PredCorr.mu x s / 4 ∧
      stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ≤
        stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ∧
      4 * β * γ / n ≤ stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) := by sorry

end AdaptiveStepIPM.WideNbhd

