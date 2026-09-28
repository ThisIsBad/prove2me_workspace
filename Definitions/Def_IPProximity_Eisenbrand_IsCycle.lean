import Mathlib

namespace IPProximity.Eisenbrand

/-- Eq. (14) of Eisenbrand–Weismantel (p. 5:7), taken literally: an integer vector `y` is a
*cycle* of `z - x` if `A y = 0` and, for each `i`, `|yᵢ| ≤ |(z - x)ᵢ|` and `yᵢ · (z - x)ᵢ ≥ 0`.
The zero vector is always a cycle. -/
def IsCycle {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (z : Fin n → ℤ) (x : Fin n → ℝ)
    (y : Fin n → ℤ) : Prop :=
  Matrix.mulVec A y = 0 ∧
    ∀ i, |(y i : ℝ)| ≤ |(z i : ℝ) - x i| ∧ 0 ≤ (y i : ℝ) * ((z i : ℝ) - x i)

end IPProximity.Eisenbrand
