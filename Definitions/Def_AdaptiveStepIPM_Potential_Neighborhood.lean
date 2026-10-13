import Mathlib
import Definitions.Def_AdaptiveStepIPM_Potential_StandardLP
import Definitions.Def_AdaptiveStepIPM_PredCorr_Neighborhoods

/-!
Mizuno, Todd, Ye, *On adaptive-step primal-dual interior-point algorithms for linear
programming*, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), §1, pp. 1–2.

Given the standard-form pair and `F⁰` in `StandardLP`, the duality measure `μ = xᵀs/n`, the one-sided seminorm
`‖z‖⁻_∞ := ‖z⁻‖_∞` with `(z⁻)_j := min{z_j, 0}`, and the neighbourhood
`N_∞⁻(β) = {(x, s) ∈ F⁰ : ‖Xs − μe‖⁻_∞ ≤ βμ}`.

Indices: the paper's `j = 1, …, n` is `j : Fin n` (`j ↦ j − 1`).
-/

open Matrix

namespace AdaptiveStepIPM.Potential

/-- `‖z‖⁻_∞ := ‖z⁻‖_∞` with `(z⁻)_j = min{z_j, 0}` (p. 2). The norm on `Fin n → ℝ` is
Mathlib's sup norm, i.e. the `ℓ_∞` norm `max_j |·|` (and `0` when `n = 0`). -/
noncomputable def negInfNorm {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  ‖fun j => min (z j) 0‖

/-- The vector `Xs − μe`, with components `x_j s_j − μ`. -/
noncomputable def centralityResidual {n : ℕ} (x s : Fin n → ℝ) : Fin n → ℝ :=
  fun j => x j * s j - AdaptiveStepIPM.PredCorr.mu x s

/-- The neighbourhood `N_∞⁻(β) = {(x, s) ∈ F⁰ : ‖Xs − μe‖⁻_∞ ≤ βμ}` (p. 2). -/
def InNinfMinus {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β : ℝ) (x s : Fin n → ℝ) : Prop :=
  (⟨A, b, c⟩ : StandardLP m n).StrictlyFeasible x s ∧
    negInfNorm (centralityResidual x s) ≤ β * AdaptiveStepIPM.PredCorr.mu x s

end AdaptiveStepIPM.Potential
