import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_FactorModel

namespace BoydADMM.Nonconvex

/-- §9.1.2, p. 75: eliminating the nonnegative diagonal gives the stated
componentwise loss, attained at `d_i = (Σ_ii - X_ii)_+`. -/
theorem factor_model_partial_minimization {n : ℕ} (Sigma X : SqMat n)
    (hn : 0 < n) (hSigma : IsSymmetric Sigma) (hX : IsSymmetric X) :
    factorLoss Sigma X = factorLossExplicit Sigma X ∧
    (∀ i, 0 ≤ optimalDiag Sigma X i) ∧
    factorLossWithDiag Sigma X (optimalDiag Sigma X) = factorLoss Sigma X := by sorry

end BoydADMM.Nonconvex

