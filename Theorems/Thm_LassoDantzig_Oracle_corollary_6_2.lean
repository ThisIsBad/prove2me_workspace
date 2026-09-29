import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Corollary 6.2** (p. 13), with the explicit `C(ε) = 4(2 + ε)²/(ε(1 + ε))` of Theorem 6.1.
Same noise, `s` and Lasso as in Theorem 6.1, but no RE assumption. For all `n ≥ 1`, `ε > 0` and
`γ > 0`, with probability at least `1 − M^{1−A²/8}`, every Lasso solution `β̂_L` satisfies, for every
`β ∈ Λ̄_{s,γ,ε} = {β ∈ Λ_{s,γ,(3+4/ε)f_max/f_min} : 𝓜(β) ≤ s}`,
`‖f̂_L − f‖_n² ≤ (1 + ε) (‖f_β − f‖_n² + C(ε) f_max² A² σ² / γ² · 𝓜(β) log M / n)`. -/
theorem corollary_6_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0) (f : Fin n → ℝ)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (A : ℝ) (hA : 2 * Real.sqrt 2 < A)
    (ε : ℝ) (hε : 0 < ε) (γ : ℝ) (hγ : 0 < γ) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ, IsLasso X (fun i => f i + W i ω) (tuning n M A σ) βhat →
        ∀ β ∈ LambdaSet X s γ ((3 + 4 / ε) * fmax X / fmin X), sparsity β ≤ s →
          empSq (fun i => X.mulVec βhat i - f i) ≤
            (1 + ε) * (empSq (fun i => X.mulVec β i - f i) +
              4 * (2 + ε) ^ 2 / (ε * (1 + ε)) * fmax X ^ 2 * A ^ 2 * σ ^ 2 / γ ^ 2 *
                ((sparsity β : ℝ) * Real.log M / n)) := by sorry

end LassoDantzig.Oracle
