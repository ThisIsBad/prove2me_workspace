import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_HasSupport
import Definitions.Def_HighDimStat_SparseLinear_RestrictedEigenvalue
import Definitions.Def_HighDimStat_SparseLinear_IsLagrangianLassoSolution
import Definitions.Def_HighDimStat_SparseLinear_L1Norm
import Definitions.Def_HighDimStat_SparseLinear_LInftyNorm

namespace HighDimStat.SparseLinear

/-- **Theorem 7.13(a)**, Wainwright, *High-Dimensional Statistics* (2019), Eq. (7.25a) and the
final sentence, p. 210. Under (A1) `θ*` is supported on `S ⊆ {1,...,d}` with `|S| = s`, and
(A2) the design matrix `X` satisfies the restricted eigenvalue condition over `S` with
parameters `(κ, 3)`: any solution `θhat` of the Lagrangian Lasso (7.18), observing
`y = Xθ* + w`, with regularization parameter `λₙ ≥ 2‖Xᵀw/n‖∞`, satisfies
`‖θhat − θ*‖₂ ≤ (3/κ)√s λₙ`; in addition, `‖θhat − θ*‖₁ ≤ 4√s‖θhat − θ*‖₂`. -/
theorem lasso_l2_error_bound {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (θstar θhat : Fin d → ℝ) (S : Finset (Fin d)) (κ lam : ℝ)
    (hSupport : HasSupport θstar S)
    (hκ : 0 < κ)
    (hRE : RestrictedEigenvalue X S κ 3)
    (hlam : 2 * linfNorm (fun j => X.transpose.mulVec w j / (n : ℝ)) ≤ lam)
    (hsol : IsLagrangianLassoSolution X (X.mulVec θstar + w) lam θhat) :
    Real.sqrt (∑ j, (θhat j - θstar j) ^ 2) ≤ (3 / κ) * Real.sqrt (S.card : ℝ) * lam ∧
    l1Norm (fun j => θhat j - θstar j) ≤
      4 * Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j, (θhat j - θstar j) ^ 2) := by sorry

end HighDimStat.SparseLinear

