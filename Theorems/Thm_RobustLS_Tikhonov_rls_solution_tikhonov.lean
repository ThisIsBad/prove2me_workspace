import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- **Theorem 3.2** of El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with
Uncertain Data*, SIAM J. Matrix Anal. Appl. 18(4) (1997), p. 1040 (PDF p. 6), with the identity
`µ = ‖Ax − b‖/√(‖x‖² + 1)` from the last display of its proof (p. 1041, PDF p. 7):
"When ρ = 1, the (unique) solution x_RLS to the RLS problem is given by
(17) x_RLS = (µI + AᵀA)⁻¹Aᵀb if µ ≜ (λ − τ)/τ > 0, A†b else,
where (λ, τ) are the (unique) optimal points for problem (15)."

Let `(x, λ, τ)` be an optimal point of the SOCP (15)
`minimize λ subject to ‖Ax − b‖ ≤ λ − τ, ‖[x; 1]‖ ≤ τ` (by Theorem 3.1, its `x`-part is the RLS
solution `x_RLS` for `ρ = 1`), and put `µ = (λ − τ)/τ`. Then
* if `µ > 0`, `x = (µI + AᵀA)⁻¹Aᵀb`;
* otherwise, `x = A†b`, i.e. `x` is the minimum-norm solution of `Ax = b`;
* in either case `µ = ‖Ax − b‖/√(‖x‖² + 1)`.

`⁻¹` is Mathlib's matrix inverse; for `µ > 0` the matrix `µI + AᵀA` is positive definite, so this
is the genuine inverse. `τ ≥ √(‖x‖² + 1) ≥ 1` for every feasible point, so the division defining
`µ` is by a positive number. -/
theorem rls_solution_tikhonov {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (hopt : IsSOCPOptimal A b x lam tau) :
    (0 < (lam - tau) / tau →
        x = (((lam - tau) / tau) • (1 : Matrix (Fin m) (Fin m) ℝ) + Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)) ∧
      (¬ 0 < (lam - tau) / tau → IsMinNormSolution A b x) ∧
      (lam - tau) / tau = eucNorm (A *ᵥ x - b) / Real.sqrt (eucNorm x ^ 2 + 1) := by sorry

end RobustLS.Tikhonov

