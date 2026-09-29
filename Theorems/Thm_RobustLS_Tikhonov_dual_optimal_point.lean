import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, p. 1041 (PDF p. 7):
"Using ‖z‖ ≤ 1, ‖[uᵀ v]ᵀ‖ ≤ 1, u = −Aᵀz, we get
z = −(Ax − b)/‖Ax − b‖ and [uᵀ v] = −[xᵀ 1]/√(‖x‖² + 1)."

Setting of the sentence: `(x, λ, τ)` is optimal for the SOCP (15) with `λ > τ`, and `(z, u, v)`
is a dual feasible point whose objective equals the primal optimal value, `bᵀz − v = λ`
(Eq. (18)). Then `z = −(Ax − b)/‖Ax − b‖` and `[u; v] = −[x; 1]/√(‖x‖² + 1)`. -/
theorem dual_optimal_point {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ)
    (hopt : IsSOCPOptimal A b x lam tau) (hlt : tau < lam) (hfeas : IsDualFeasible A z u v)
    (hval : b ⬝ᵥ z - v = lam) :
    z = (-(1 / eucNorm (A *ᵥ x - b))) • (A *ᵥ x - b) ∧
      stackScalar u v = (-(1 / Real.sqrt (eucNorm x ^ 2 + 1))) • stackOne x := by sorry

end RobustLS.Tikhonov
