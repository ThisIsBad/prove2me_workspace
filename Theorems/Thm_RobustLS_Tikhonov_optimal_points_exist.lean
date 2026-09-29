import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, p. 1041 (PDF p. 7):
"Since both primal and dual problems are strictly feasible, there exist optimal points for both
of them."

For every `A ∈ ℝ^{n×m}` and `b ∈ ℝ^n`, the SOCP (15)
`minimize λ subject to ‖Ax − b‖ ≤ λ − τ, ‖[x; 1]‖ ≤ τ`
has an optimal point `(x, λ, τ)`, and its dual
`maximize bᵀz − v subject to Aᵀz + u = 0, ‖z‖ ≤ 1, ‖[u; v]‖ ≤ 1`
has an optimal point `(z, u, v)`. -/
theorem optimal_points_exist {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) :
    (∃ (x : Fin m → ℝ) (lam tau : ℝ), IsSOCPOptimal A b x lam tau) ∧
      (∃ (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ), IsDualOptimal A b z u v) := by sorry

end RobustLS.Tikhonov
