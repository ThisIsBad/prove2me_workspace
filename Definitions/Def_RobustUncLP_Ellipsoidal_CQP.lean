import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting

namespace RobustUncLP.Ellipsoidal

open Matrix

/-- Data of a generic conic quadratic problem `(CQP_p)`, Appendix, p. 15: design vector
`z ∈ ℝ^N`, `p` linear equations `Rz = r`, and `k + 1` conic constraints
`‖A_ℓ z − b_ℓ‖ ≤ c_ℓᵀz − d_ℓ` (`A_ℓ` has `q ℓ` rows); objective `eᵀz + φ`. -/
structure CQPData (N p k : ℕ) where
  q : Fin (k + 1) → ℕ
  R : Matrix (Fin p) (Fin N) ℝ
  r : Fin p → ℝ
  A : (ℓ : Fin (k + 1)) → Matrix (Fin (q ℓ)) (Fin N) ℝ
  b : (ℓ : Fin (k + 1)) → Fin (q ℓ) → ℝ
  c : Fin (k + 1) → Fin N → ℝ
  d : Fin (k + 1) → ℝ
  e : Fin N → ℝ
  φ : ℝ

namespace CQPData

variable {N p k : ℕ}

/-- Feasible set of `(CQP_p)`. -/
def primalFeas (P : CQPData N p k) : Set (Fin N → ℝ) :=
  {z | P.R *ᵥ z = P.r ∧ ∀ ℓ, euclidNorm (P.A ℓ *ᵥ z - P.b ℓ) ≤ P.c ℓ ⬝ᵥ z - P.d ℓ}

/-- Objective `eᵀz + φ` of `(CQP_p)`. -/
def primalObj (P : CQPData N p k) (z : Fin N → ℝ) : ℝ :=
  P.e ⬝ᵥ z + P.φ

/-- Feasible set of the dual `(CQP_d)`: `w = (λ, μ, ν)` with
`Rᵀλ + ∑_{ℓ=0}^k [ν_ℓ c_ℓ + A_ℓᵀ μ_ℓ] = e` and `‖μ_ℓ‖ ≤ ν_ℓ` for `ℓ = 0, …, k`. -/
def dualFeas (P : CQPData N p k) :
    Set ((Fin p → ℝ) × ((ℓ : Fin (k + 1)) → Fin (P.q ℓ) → ℝ) × (Fin (k + 1) → ℝ)) :=
  {w | P.Rᵀ *ᵥ w.1 + ∑ ℓ, (w.2.2 ℓ • P.c ℓ + (P.A ℓ)ᵀ *ᵥ w.2.1 ℓ) = P.e ∧
    ∀ ℓ, euclidNorm (w.2.1 ℓ) ≤ w.2.2 ℓ}

/-- Objective `rᵀλ + ∑_{ℓ=0}^k [d_ℓ ν_ℓ + b_ℓᵀ μ_ℓ] + φ` of `(CQP_d)`. -/
def dualObj (P : CQPData N p k)
    (w : (Fin p → ℝ) × ((ℓ : Fin (k + 1)) → Fin (P.q ℓ) → ℝ) × (Fin (k + 1) → ℝ)) : ℝ :=
  P.r ⬝ᵥ w.1 + ∑ ℓ, (P.d ℓ * w.2.2 ℓ + P.b ℓ ⬝ᵥ w.2.1 ℓ) + P.φ

end CQPData

end RobustUncLP.Ellipsoidal
