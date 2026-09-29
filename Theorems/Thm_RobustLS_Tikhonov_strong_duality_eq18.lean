import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, Eq. (18), p. 1041 (PDF p. 7):
"Now assume λ > τ. Again, both primal and dual problems are strictly feasible; therefore, the
primal- and dual-optimal objectives are equal:
(18) ‖Ax − b‖ + ‖[xᵀ 1]‖ = λ = bᵀz − v = −(Ax − b)ᵀz − [xᵀ 1][−Aᵀz; v]."

If `(x, λ, τ)` is optimal for the SOCP (15) with `λ > τ` and `(z, u, v)` is optimal for its
dual, then the chain of equalities (18) holds. -/
theorem strong_duality_eq18 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ)
    (hopt : IsSOCPOptimal A b x lam tau) (hlt : tau < lam) (hdual : IsDualOptimal A b z u v) :
    eucNorm (A *ᵥ x - b) + eucNorm (stackOne x) = lam ∧
      lam = b ⬝ᵥ z - v ∧
      b ⬝ᵥ z - v = -((A *ᵥ x - b) ⬝ᵥ z) - stackOne x ⬝ᵥ stackScalar (-(Aᵀ *ᵥ z)) v := by sorry

end RobustLS.Tikhonov

