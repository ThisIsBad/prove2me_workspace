import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, p. 1041 (PDF p. 7):
"If λ = τ at the optimum, then Ax = b, and λ = τ = √(‖x‖² + 1)."

If `(x, λ, τ)` is an optimal point of the SOCP (15) and `λ = τ`, then `Ax = b` and
`λ = τ = √(‖x‖² + 1)`. -/
theorem optimum_lam_eq_tau {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (hopt : IsSOCPOptimal A b x lam tau) (heq : lam = tau) :
    A *ᵥ x = b ∧ lam = Real.sqrt (eucNorm x ^ 2 + 1) ∧ tau = Real.sqrt (eucNorm x ^ 2 + 1) := by sorry

end RobustLS.Tikhonov
