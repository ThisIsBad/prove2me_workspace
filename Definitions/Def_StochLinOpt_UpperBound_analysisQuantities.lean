import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2

open Matrix

namespace StochLinOpt.UpperBound

/-- The normalized width `w_t = √(x_tᵀ A_t⁻¹ x_t)`. -/
noncomputable def width {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : ℝ :=
  Real.sqrt (x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t))

/-- The cumulative regret `R_T = ∑_{t=1}^T (µ ⬝ᵥ x_t - µ ⬝ᵥ x*)` (`R_0 = 0`). -/
def regret {n : ℕ} (μ xstar : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar)

/-- `Z_t = (µ̂_t - µ)ᵀ A_t (µ̂_t - µ)`. -/
noncomputable def zStat {n : ℕ} (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ) : ℝ :=
  (muHat x ℓ t - μ) ⬝ᵥ (designMatrix x t *ᵥ (muHat x ℓ t - μ))

open Classical in
/-- The indicator `E_t = 𝟙{Z_τ ≤ β_τ for all 1 ≤ τ ≤ t}`. -/
noncomputable def escapeInd {n : ℕ} (δ : ℝ) (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (t : ℕ) : ℝ :=
  if ∀ τ ∈ Finset.Icc 1 t, zStat μ x ℓ τ ≤ beta n δ τ then 1 else 0

/-- The martingale increment `M_t = 2 η_t E_t x_tᵀ(µ̂_t - µ) / (1 + w_t²)` with noise
`η_t = ℓ_t - µ ⬝ᵥ x_t`. -/
noncomputable def mIncrement {n : ℕ} (δ : ℝ) (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (t : ℕ) : ℝ :=
  2 * (ℓ t - μ ⬝ᵥ x t) * escapeInd δ μ x ℓ t * (x t ⬝ᵥ (muHat x ℓ t - μ)) /
    (1 + width x t ^ 2)

end StochLinOpt.UpperBound
