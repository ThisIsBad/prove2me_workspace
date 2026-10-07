import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

namespace BoydADMM.ModelFit

open Matrix

/-! Objects of Chapter 8 (distributed model fitting) of Boyd–Parikh–Chu–Peleato–Eckstein (2011),
pp. 61–72. Vectors live in `EuclideanSpace ℝ (Fin n)`, so `‖·‖` is the Euclidean norm `‖·‖₂`; a
matrix `A ∈ ℝ^{m×n}` acts by `Matrix.toEuclideanLin A`, and `Aᵀ` by `Matrix.toEuclideanLin Aᵀ`.
The regularization weight `λ` of the book is called `lam` (`λ` is a Lean keyword). -/

/-- The shifted soft thresholding operation of §8.3.4 (p. 71), for `N` blocks and penalty `ρ`:
`a − N/ρ` if `a > −1/N + N/ρ`, `−1/N` if `a ∈ [−1/N, −1/N + N/ρ]`, `a` if `a < −1/N`. -/
noncomputable def shiftedSoftThreshold (N : ℕ) (ρ a : ℝ) : ℝ :=
  if -1 / (N : ℝ) + N / ρ < a then a - N / ρ
  else if a < -1 / (N : ℝ) then a else -1 / (N : ℝ)

/-- The ℓ1 norm `‖x‖₁ = ∑ⱼ |xⱼ|` of a vector. -/
noncomputable def l1norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j, |x j|

/-- The group-lasso block objective of §8.3.2 (p. 69):
`h(x) = (ρ/2)‖A x − v‖₂² + λ‖x‖₂` for `x ∈ ℝⁿ`, with `A ∈ ℝ^{m×n}` and `v ∈ ℝᵐ`. -/
noncomputable def groupLassoObj {m n : ℕ} (ρ lam : ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ρ / 2 * ‖Matrix.toEuclideanLin A x - v‖ ^ 2 + lam * ‖x‖

/-- The ridge point `(AᵀA + νI)⁻¹ Aᵀ v` of §8.3.2 (p. 69). For `ν > 0` the matrix `AᵀA + νI` is
positive definite, so `⁻¹` is the true inverse. -/
noncomputable def ridgeSol {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ν : ℝ)
    (v : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin ((Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ * Aᵀ) v

end BoydADMM.ModelFit
