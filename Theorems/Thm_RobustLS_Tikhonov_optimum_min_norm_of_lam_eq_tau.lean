import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, p. 1041 (PDF p. 7):
"In this case, the optimal x is the (unique) minimum-norm solution to Ax = b: x = A†b."

"This case" is `λ = τ` at the optimum of the SOCP (15). If `(x, λ, τ)` is optimal for (15) and
`λ = τ`, then `x` is a minimum-norm solution of `Ax = b` (i.e. `x = A†b`; the minimum-norm
solution of a consistent system is unique, so `IsMinNormSolution` pins down `A†b`). -/
theorem optimum_min_norm_of_lam_eq_tau {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (x : Fin m → ℝ) (lam tau : ℝ) (hopt : IsSOCPOptimal A b x lam tau)
    (heq : lam = tau) :
    IsMinNormSolution A b x := by sorry

end RobustLS.Tikhonov
