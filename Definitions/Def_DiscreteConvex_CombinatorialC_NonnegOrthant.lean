import Mathlib

namespace DiscreteConvex.CombinatorialC

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p. 74: `F(w,c)` is defined for capacities
`c ∈ ℝ^A_+` only. For a capacity with a negative entry no circulation is feasible and the real
supremum defining `F` returns `0`, which breaks the concavity of Proposition 2.21 and the `c`
parts of Theorems 2.22 and 2.23 (one loop arc, `w > 0`, capacities `-1, 1, 0` give `F` values
`0, w, 0`). The `c` parts are therefore stated on the nonnegative orthant, where the feasible
set contains `0` and is bounded so the supremum is genuine.
-/

/-- The nonnegative orthant `ℝ^W_+`. -/
def NonnegOrthant {W : Type*} : Set (W → ℝ) := {x | 0 ≤ x}

end DiscreteConvex.CombinatorialC
