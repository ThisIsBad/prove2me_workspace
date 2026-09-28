import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic

namespace CaiCandesShen.Convergence

open Matrix

/-- `(U, σ, V)` is a reduced singular value decomposition of `Y` of rank `r` (eq. (2.1), p. 1959):
`U` is `n₁ × r` and `V` is `n₂ × r` with orthonormal columns, the singular values `σ_i` are
positive, and `Y = U diag(σ) V*`. -/
def IsReducedSVD {n₁ n₂ : ℕ} (Y : Mat n₁ n₂) (r : ℕ) (U : Matrix (Fin n₁) (Fin r) ℝ)
    (σ : Fin r → ℝ) (V : Matrix (Fin n₂) (Fin r) ℝ) : Prop :=
  Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (∀ i, 0 < σ i) ∧ Y = U * diagonal σ * Vᵀ

/-- `X = D_τ(Y)`, the singular value shrinkage (soft-thresholding) operator of eq. (2.2), p. 1959:
for some reduced SVD `Y = U diag(σ) V*`, `X = U diag((σ_i - τ)_+) V*`, where `t_+ = max(0, t)`. -/
def IsShrink {n₁ n₂ : ℕ} (τ : ℝ) (Y X : Mat n₁ n₂) : Prop :=
  ∃ (r : ℕ) (U : Matrix (Fin n₁) (Fin r) ℝ) (σ : Fin r → ℝ) (V : Matrix (Fin n₂) (Fin r) ℝ),
    IsReducedSVD Y r U σ V ∧ X = U * diagonal (fun i => max (σ i - τ) 0) * Vᵀ

end CaiCandesShen.Convergence
