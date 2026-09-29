import Mathlib

namespace HighDimProb.RandomMatrices

/-- The operator (spectral) norm of an `m × n` real matrix, Vershynin, *High-Dimensional
Probability* (2018), §4.1.2, p. 77: `‖A‖ := ‖A : ℓⁿ₂ → ℓᵐ₂‖ = maxₓ∈Sⁿ⁻¹ ‖Ax‖₂`. `A` acts as a
continuous linear map between the finite-dimensional Euclidean spaces `EuclideanSpace ℝ (Fin n)`
and `EuclideanSpace ℝ (Fin m)` (every linear map between finite-dimensional normed spaces is
automatically continuous, `LinearMap.toContinuousLinearMap`), and `matrixOpNorm` is its
`ContinuousLinearMap` operator norm, which for a finite-dimensional domain agrees with the
book's `maxₓ∈Sⁿ⁻¹ ‖Ax‖₂` (the sup over the unit ball of a continuous linear map is attained on
the sphere by linearity, and is attained at all since the unit ball is compact). -/
noncomputable def matrixOpNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))‖

end HighDimProb.RandomMatrices
