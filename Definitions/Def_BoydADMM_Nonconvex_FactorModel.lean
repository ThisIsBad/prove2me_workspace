import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_MatrixBasics

namespace BoydADMM.Nonconvex

/-- The factor-model loss before eliminating the nonnegative diagonal `d` (§9.1.2, p. 75). -/
noncomputable def factorLossWithDiag {n : ℕ} (Sigma X : SqMat n) (d : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * frobSq (X + diag d - Sigma)

/-- The book's `f(X) = inf_{d ≥ 0} (1/2) ‖X + diag(d) - Σ‖²_F`. -/
noncomputable def factorLoss {n : ℕ} (Sigma X : SqMat n) : ℝ :=
  sInf {r : ℝ | ∃ d : Fin n → ℝ, (∀ i, 0 ≤ d i) ∧
    r = factorLossWithDiag Sigma X d}

/-- The componentwise formula for `f` printed in §9.1.2. -/
noncomputable def factorLossExplicit {n : ℕ} (Sigma X : SqMat n) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, if i ≠ j then (X i j - Sigma i j) ^ 2 else 0) +
    (1 / 2 : ℝ) * ∑ i, (max (X i i - Sigma i i) 0) ^ 2

/-- The minimizing nonnegative diagonal `d_i = (Σ_ii - X_ii)_+`. -/
def optimalDiag {n : ℕ} (Sigma X : SqMat n) : Fin n → ℝ :=
  fun i => max (Sigma i i - X i i) 0

/-- The scaled-dual `X`-subproblem objective at a step with data `Z`, `U`. -/
noncomputable def xSubproblem {n : ℕ} (Sigma Z U : SqMat n) (rho : ℝ)
    (X : SqMat n) : ℝ :=
  factorLoss Sigma X + (rho / 2) * frobSq (X - Z + U)

/-- The book's entrywise `X`-update, with the missing `k` superscripts in the
diagonal case condition restored (§9.1.2, p. 75). -/
noncomputable def xUpdate {n : ℕ} (Sigma Z U : SqMat n) (rho : ℝ) : SqMat n :=
  fun i j =>
    if i = j then
      if Sigma i i ≤ Z i i - U i i then
        (Sigma i i + rho * (Z i i - U i i)) / (1 + rho)
      else Z i i - U i i
    else (Sigma i j + rho * (Z i j - U i j)) / (1 + rho)

end BoydADMM.Nonconvex
