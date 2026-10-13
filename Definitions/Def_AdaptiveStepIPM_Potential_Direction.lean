import Mathlib
import Definitions.Def_AdaptiveStepIPM_Potential_Neighborhood
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

/-!
Mizuno, Todd, Ye, Cornell ORIE TR 944 (1990, rev. 1991), §2 (p. 4) and §4 (Lemma 5, p. 10).

The search direction `d = (d_x, d_y, d_s)` of system (2), the line `x(θ) = x + θd_x`,
`s(θ) = s + θd_s` of (3), the scaled vectors `p = X^{-1/2}S^{1/2}d_x`, `q = X^{1/2}S^{-1/2}d_s`
of (6), the componentwise product `Pq = (p_j q_j)_j`, and the step bound
`θ₂⁻ = min{1, βγμ/‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞}` of Lemma 5.
-/

open Matrix

namespace AdaptiveStepIPM.Potential

/-- `d = (d_x, d_y, d_s)` solves system (2) at `(x, s)` with parameter `γ` (p. 4):
`S d_x + X d_s = γμe − Xs`, `A d_x = 0`, `Aᵀ d_y + d_s = 0`, where `μ = xᵀs/n`. -/
def IsNewtonDirection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (γ : ℝ)
    (x s : Fin n → ℝ) (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  (∀ j, s j * dx j + x j * ds j = γ * AdaptiveStepIPM.PredCorr.mu x s - x j * s j) ∧
  A *ᵥ dx = 0 ∧ Aᵀ *ᵥ dy + ds = 0

/-- The point `v + θ d` on the line (3): `x(θ) = x + θ d_x` and `s(θ) = s + θ d_s`. -/
def lineStep {n : ℕ} (v d : Fin n → ℝ) (θ : ℝ) : Fin n → ℝ :=
  fun j => v j + θ * d j

/-- `p := X^{-0.5} S^{0.5} d_x`, i.e. `p_j = √(s_j/x_j) (d_x)_j` (6). -/
noncomputable def pVec {n : ℕ} (x s dx : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (s j / x j) * dx j

/-- `q := X^{0.5} S^{-0.5} d_s`, i.e. `q_j = √(x_j/s_j) (d_s)_j` (6). -/
noncomputable def qVec {n : ℕ} (x s ds : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (x j / s j) * ds j

/-- `θ₂⁻ := min{1, βγμ/‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞}` (Lemma 5, p. 10), with `μ = xᵀs/n`.
When `‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞ = 0` the quotient is read as `+∞`, so `θ₂⁻ := 1`. -/
noncomputable def theta2Minus {n : ℕ} (β γ : ℝ) (x s dx ds : Fin n → ℝ) : ℝ :=
  if negInfNorm (AdaptiveStepIPM.PredCorr.Pq x s dx ds) = 0 then 1
  else min 1 (β * γ * AdaptiveStepIPM.PredCorr.mu x s / negInfNorm (AdaptiveStepIPM.PredCorr.Pq x s dx ds))

end AdaptiveStepIPM.Potential
