import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Neighborhoods

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- The strictly feasible primal-dual pairs `F⁰` of Mizuno–Todd–Ye, §1, p. 1: pairs `(x, s)` with
`x > 0`, `s > 0`, `Ax = b`, and `Aᵀy + s = c` for some `y ∈ ℝᵐ`. -/
def strictlyFeasible {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ j, 0 < p.1 j) ∧ (∀ j, 0 < p.2 j) ∧ A *ᵥ p.1 = b ∧ ∃ y : Fin m → ℝ, Aᵀ *ᵥ y + p.2 = c}

/-- The usual `ℓ_∞` norm `‖z‖_∞ = max_j |z_j|` (p. 2), written as a supremum over the finitely
many coordinates (it is `0` when `n = 0`). -/
noncomputable def normInf {n : ℕ} (z : Fin n → ℝ) : ℝ := ⨆ j, |z j|

/-- `‖z‖⁻_∞ := ‖z⁻‖_∞` with `(z⁻)_j := min{z_j, 0}` (p. 2). -/
noncomputable def normInfNeg {n : ℕ} (z : Fin n → ℝ) : ℝ := normInf (fun j => min (z j) 0)

/-- `‖z‖⁺_∞ := ‖z⁺‖_∞` with `(z⁺)_j := max{z_j, 0}` (p. 2). -/
noncomputable def normInfPos {n : ℕ} (z : Fin n → ℝ) : ℝ := normInf (fun j => max (z j) 0)

/-- The Euclidean norm `‖z‖ = (∑_j z_j²)^{1/2}`; on p. 2, `‖·‖` without subscript is the `ℓ₂`
norm. (Mathlib's default norm on `Fin n → ℝ` is the sup norm, hence the explicit definition.) -/
noncomputable def norm2 {n : ℕ} (z : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, z j ^ 2)

/-- The wide neighbourhood `N_∞(β) = {(x, s) ∈ F⁰ : ‖Xs − μe‖_∞ ≤ βμ}`, `μ = xᵀs/n` (p. 2). -/
def Ninf {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (β : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ strictlyFeasible A b c ∧
    normInf (fun j => p.1 j * p.2 j - AdaptiveStepIPM.PredCorr.mu p.1 p.2) ≤ β * AdaptiveStepIPM.PredCorr.mu p.1 p.2}

/-- The wide neighbourhood `N_∞⁻(β) = {(x, s) ∈ F⁰ : ‖Xs − μe‖⁻_∞ ≤ βμ}`, `μ = xᵀs/n` (p. 2). -/
def NinfMinus {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (β : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ strictlyFeasible A b c ∧
    normInfNeg (fun j => p.1 j * p.2 j - AdaptiveStepIPM.PredCorr.mu p.1 p.2) ≤ β * AdaptiveStepIPM.PredCorr.mu p.1 p.2}

end AdaptiveStepIPM.WideNbhd
