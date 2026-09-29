import Mathlib

/-!
Slopes and paired hyperplanes (Megiddo, J. ACM 31 (1984), §3.2, p. 119).

The hyperplane `H = {x ∈ ℝ^d | a ⬝ᵥ x = b}` meets the `(x₁, x₂)` plane in the line
`a₁x₁ + a₂x₂ = b`; its *slope* is `+∞` if `a₂ = 0` and `-a₁/a₂` otherwise. The paper's
coordinates `x₁, x₂` are the indices `0, 1` of `Fin (d + 2)` (the paper's dimension is
`d + 2 ≥ 2`). For a pair `H_i, H_k` the paper defines
`H⁽¹⁾_ik : Σⱼ (a_k1 a_ij - a_i1 a_kj) xⱼ = a_k1 bᵢ - a_i1 b_k` and
`H⁽²⁾_ik : Σⱼ (a_k2 a_ij - a_i2 a_kj) xⱼ = a_k2 bᵢ - a_i2 b_k`.
-/

namespace MegiddoLP.FixedDim

variable {d : ℕ}

/-- The hyperplane with normal `a` has nonnegative slope in the `(x₁, x₂)` plane: its slope
is `+∞` (`a₂ = 0`) or `-a₁/a₂ ≥ 0`. -/
def HasNonnegSlope (a : Fin (d + 2) → ℝ) : Prop :=
  a 1 = 0 ∨ 0 ≤ -(a 0) / a 1

/-- The hyperplane with normal `a` has nonpositive slope in the `(x₁, x₂)` plane: `a₂ ≠ 0`
and `-a₁/a₂ ≤ 0` (a slope `+∞` is not nonpositive). -/
def HasNonposSlope (a : Fin (d + 2) → ℝ) : Prop :=
  a 1 ≠ 0 ∧ -(a 0) / a 1 ≤ 0

/-- Normal vector of `H⁽¹⁾_ik`: `j ↦ a_k1 a_ij - a_i1 a_kj`. -/
def pairNormal1 (ai ak : Fin (d + 2) → ℝ) : Fin (d + 2) → ℝ :=
  fun j => ak 0 * ai j - ai 0 * ak j

/-- Right-hand side of `H⁽¹⁾_ik`: `a_k1 bᵢ - a_i1 b_k`. -/
def pairRhs1 (ai ak : Fin (d + 2) → ℝ) (bi bk : ℝ) : ℝ :=
  ak 0 * bi - ai 0 * bk

/-- Normal vector of `H⁽²⁾_ik`: `j ↦ a_k2 a_ij - a_i2 a_kj`. -/
def pairNormal2 (ai ak : Fin (d + 2) → ℝ) : Fin (d + 2) → ℝ :=
  fun j => ak 1 * ai j - ai 1 * ak j

/-- Right-hand side of `H⁽²⁾_ik`: `a_k2 bᵢ - a_i2 b_k`. -/
def pairRhs2 (ai ak : Fin (d + 2) → ℝ) (bi bk : ℝ) : ℝ :=
  ak 1 * bi - ai 1 * bk

end MegiddoLP.FixedDim
