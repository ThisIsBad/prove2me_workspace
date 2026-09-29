import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **(B.4)** (Bickel–Ritov–Tsybakov, p. 21, proof of Lemma B.1). Let `W_1, …, W_n` be independent
`N(0, σ²)`, `σ > 0`, and `r = Aσ√(log M / n)` with `A > 2√2`. The event
`𝒜 = ⋂_j {2|V_j| ≤ r‖f_j‖_n}`, `V_j = n⁻¹ ∑ᵢ f_j(Z_i) W_i`, is measurable and
`P(𝒜ᶜ) ≤ M^{1 − A²/8}`. -/
theorem eq_B4_noise_event {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) :
    MeasurableSet (noiseEvent X W (tuning n M A σ)) ∧
      P (noiseEvent X W (tuning n M A σ))ᶜ ≤ ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by sorry

end LassoDantzig.Oracle
