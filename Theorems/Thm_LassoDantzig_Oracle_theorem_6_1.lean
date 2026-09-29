import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Theorem 6.1** (p. 13), with the constant the proof (p. 26) yields,
`C(ε) = 4(2 + ε)²/(ε(1 + ε))`. Let `W_i` be independent `N(0, σ²)`, `σ² > 0`; fix `ε > 0`,
`n ≥ 1`, `M ≥ 2`, `1 ≤ s ≤ M`, and let RE(s, (3 + 4/ε) f_max/f_min) hold with witness `κ > 0`.
Let `r = Aσ√(log M / n)` with `A > 2√2`. With probability at least `1 − M^{1−A²/8}`, every Lasso
solution `β̂_L` of (2.1) with data `y = f + W` satisfies, for every `β` with `𝓜(β) ≤ s`,
`‖f̂_L − f‖_n² ≤ (1 + ε) (‖f_β − f‖_n² + C(ε) f_max² A² σ² / κ² · 𝓜(β) log M / n)`.
The target `f` is arbitrary. -/
theorem theorem_6_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0) (f : Fin n → ℝ)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (ε : ℝ) (hε : 0 < ε) (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M)
    (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s ((3 + 4 / ε) * fmax X / fmin X) κ)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ, IsLasso X (fun i => f i + W i ω) (tuning n M A σ) βhat →
        ∀ β : Fin M → ℝ, sparsity β ≤ s →
          empSq (fun i => X.mulVec βhat i - f i) ≤
            (1 + ε) * (empSq (fun i => X.mulVec β i - f i) +
              4 * (2 + ε) ^ 2 / (ε * (1 + ε)) * fmax X ^ 2 * A ^ 2 * σ ^ 2 / κ ^ 2 *
                ((sparsity β : ℝ) * Real.log M / n)) := by sorry

end LassoDantzig.Oracle
