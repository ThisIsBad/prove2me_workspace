import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- Lemma 5 of Mizuno–Todd–Ye (p. 10): let `β, γ ∈ (0, 1)`, `(x, s)` in the neighbourhood `N`,
`d` a solution of (2) at `(x, s)` with `γ`, `μ = xᵀs/n` and `p, q` as in (6).
If `N = N_∞(β)`, every `θ ∈ [0, θ₂]` with `θ₂ = min{1, βγμ/‖AdaptiveStepIPM.PredCorr.Pq‖_∞}` keeps `(x(θ), s(θ)) ∈ N`, so
the largest admissible `θ̄` satisfies `θ̄ ≥ θ₂`; likewise for `N = N_∞⁻(β)` with
`θ₂⁻ = min{1, βγμ/‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞}`. (The minimum is `1` when the norm is `0`.) -/
theorem lemma_5 {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (x s : Fin n → ℝ) (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsDirection A x s γ dx dy ds) :
    ((x, s) ∈ Ninf A b c β →
        (∀ θ ∈ Set.Icc (0 : ℝ) (stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds))),
            (x + θ • dx, s + θ • ds) ∈ Ninf A b c β) ∧
        ∀ θbar, IsGreatest (admissibleSteps (Ninf A b c β) x s dx ds) θbar →
          stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ≤ θbar) ∧
      ((x, s) ∈ NinfMinus A b c β →
        (∀ θ ∈ Set.Icc (0 : ℝ) (stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds))),
            (x + θ • dx, s + θ • ds) ∈ NinfMinus A b c β) ∧
        ∀ θbar, IsGreatest (admissibleSteps (NinfMinus A b c β) x s dx ds) θbar →
          stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ≤ θbar) := by sorry

end AdaptiveStepIPM.WideNbhd

