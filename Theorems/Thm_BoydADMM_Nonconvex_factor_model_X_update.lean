import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_FactorModel

namespace BoydADMM.Nonconvex

/-- §9.1.2, p. 75: the printed entrywise formula, with the omitted iteration
superscripts restored, is the unique symmetric minimizer of the `X`-update. -/
theorem factor_model_X_update {n : ℕ} (Sigma Z U : SqMat n) (rho : ℝ)
    (hn : 0 < n) (hSigma : IsSymmetric Sigma) (hZ : IsSymmetric Z) (hU : IsSymmetric U)
    (hrho : 0 < rho) :
    IsSymmetric (xUpdate Sigma Z U rho) ∧
    (∀ X : SqMat n, IsSymmetric X →
      xSubproblem Sigma Z U rho (xUpdate Sigma Z U rho) ≤
        xSubproblem Sigma Z U rho X ∧
      (xSubproblem Sigma Z U rho X =
        xSubproblem Sigma Z U rho (xUpdate Sigma Z U rho) →
        X = xUpdate Sigma Z U rho)) := by sorry

end BoydADMM.Nonconvex

