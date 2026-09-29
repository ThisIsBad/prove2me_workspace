import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Lemma B.1, (B.1)** (p. 20). Fix `M ≥ 2`, `n ≥ 1`, independent `W_i ∼ N(0, σ²)` with
`σ² > 0`, and `r = Aσ√(log M / n)` with `A > 2√2`. With probability at least `1 − M^{1−A²/8}`,
simultaneously for all `β ∈ ℝ^M` and every Lasso solution `β̂_L` of (2.1) with data `y = f + W`:
`‖f̂_L − f‖_n² + r ∑_j ‖f_j‖_n |β̂_{j,L} − β_j| ≤ ‖f_β − f‖_n² + 4r ∑_{j ∈ J(β)} ‖f_j‖_n |β̂_{j,L} − β_j|
  ≤ ‖f_β − f‖_n² + 4r √𝓜(β) √(∑_{j ∈ J(β)} ‖f_j‖_n² |β̂_{j,L} − β_j|²)`. -/
theorem lemma_B1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0) (f : Fin n → ℝ)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ, IsLasso X (fun i => f i + W i ω) (tuning n M A σ) βhat →
        ∀ β : Fin M → ℝ,
          empSq (fun i => X.mulVec βhat i - f i) +
                tuning n M A σ * ∑ j, colNorm X j * |βhat j - β j| ≤
              empSq (fun i => X.mulVec β i - f i) +
                4 * tuning n M A σ * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
            empSq (fun i => X.mulVec β i - f i) +
                4 * tuning n M A σ * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ≤
              empSq (fun i => X.mulVec β i - f i) +
                4 * tuning n M A σ * Real.sqrt (sparsity β) *
                  Real.sqrt (∑ j ∈ supp β, colNorm X j ^ 2 * |βhat j - β j| ^ 2) := by sorry

end LassoDantzig.Oracle
