import Mathlib

namespace CookSensitivity.ChvatalRank

/-- `Δ(A)`: the maximum of the absolute values of the determinants of the (nonempty) square
submatrices of the integral `m × n` matrix `A`. A `(k+1) × (k+1)` submatrix is given by an
injective choice of rows `f` and of columns `g`; reordering rows or columns only changes the
sign of the determinant. The `0 × 0` submatrix is excluded, so `Δ(0) = 0`, and `Δ(A) = 0`
when `m = 0` or `n = 0`. -/
noncomputable def maxSubdet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  Finset.univ.sup fun k : Fin (min m n) =>
    Finset.univ.sup fun f : Fin (k.val + 1) ↪ Fin m =>
      Finset.univ.sup fun g : Fin (k.val + 1) ↪ Fin n =>
        (A.submatrix f g).det.natAbs

/-- The `ℓ∞`-norm `‖x‖∞ = max {|xᵢ| : i = 1, …, k}` of a rational vector (equal to `0` for
`k = 0`). -/
def supNorm {k : ℕ} (x : Fin k → ℚ) : ℚ :=
  Finset.univ.fold max 0 fun i => |x i|

/-- The `ℓ1`-norm `‖x‖₁ = ∑ |xᵢ|` of a rational vector. -/
def l1Norm {k : ℕ} (x : Fin k → ℚ) : ℚ :=
  ∑ i, |x i|

end CookSensitivity.ChvatalRank
