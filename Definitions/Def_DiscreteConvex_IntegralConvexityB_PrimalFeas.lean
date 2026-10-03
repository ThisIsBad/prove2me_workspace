import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.107, Eq. (3.45): the primal LP feasible
region, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `P = \{x ∈ Rⁿ | Ax = b, x ≥ 0\}` (Eq. (3.45)). -/
def PrimalFeas {V W : Type*} [Fintype V] (A : Matrix W V ℝ) (b : W → ℝ) : Set (V → ℝ) :=
  {x | A.mulVec x = b ∧ ∀ j, 0 ≤ x j}

end DiscreteConvex.IntegralConvexityB
