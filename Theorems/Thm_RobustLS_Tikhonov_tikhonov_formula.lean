import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, p. 1041 (PDF p. 7):
"Replace these values in Aᵀz + u = 0 to obtain the expression of the optimal x:
x = (AᵀA + µI)⁻¹Aᵀb, with µ = (λ − τ)/τ = ‖Ax − b‖/√(‖x‖² + 1)."

Setting: `(x, λ, τ)` is optimal for the SOCP (15) with `λ > τ`, and `z ∈ ℝ^n`, `u ∈ ℝ^m` satisfy
`Aᵀz + u = 0` together with the values found in the previous step,
`z = −(Ax − b)/‖Ax − b‖` and `u = −x/√(‖x‖² + 1)`. Then `µ = (λ − τ)/τ` equals
`‖Ax − b‖/√(‖x‖² + 1)` and `x = (AᵀA + µI)⁻¹Aᵀb`.

`⁻¹` is Mathlib's matrix inverse; under these hypotheses `µ > 0`, so `AᵀA + µI` is positive
definite and the inverse is the genuine one. -/
theorem tikhonov_formula {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (z : Fin n → ℝ) (u : Fin m → ℝ)
    (hopt : IsSOCPOptimal A b x lam tau) (hlt : tau < lam)
    (hlin : Aᵀ *ᵥ z + u = 0)
    (hz : z = (-(1 / eucNorm (A *ᵥ x - b))) • (A *ᵥ x - b))
    (hu : u = (-(1 / Real.sqrt (eucNorm x ^ 2 + 1))) • x) :
    (lam - tau) / tau = eucNorm (A *ᵥ x - b) / Real.sqrt (eucNorm x ^ 2 + 1) ∧
      x = (Aᵀ * A + ((lam - tau) / tau) • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ *ᵥ (Aᵀ *ᵥ b) := by sorry

end RobustLS.Tikhonov
