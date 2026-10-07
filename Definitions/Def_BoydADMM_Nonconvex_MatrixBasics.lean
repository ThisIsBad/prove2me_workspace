import Mathlib

namespace BoydADMM.Nonconvex

/-- Real square matrices, used for the symmetric factor model of §9.1.2. -/
abbrev SqMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Symmetry of a real square matrix. -/
def IsSymmetric {n : ℕ} (X : SqMat n) : Prop :=
  ∀ i j, X i j = X j i

/-- The square of the Frobenius norm, as the sum of squares of all ordered entries. -/
def frobSq {n : ℕ} (X : SqMat n) : ℝ :=
  ∑ i, ∑ j, (X i j) ^ 2

/-- The diagonal matrix with diagonal `d`. -/
def diag {n : ℕ} (d : Fin n → ℝ) : SqMat n :=
  Matrix.diagonal d

end BoydADMM.Nonconvex
