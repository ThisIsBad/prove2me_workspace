import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.90, Eq. (3.52): the discrete Minkowski sum, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `S1 + S2 = \{x1+x2 | x1 ∈ S1, x2 ∈ S2\}` (Eq. (3.52)), the discrete (integral) Minkowski
sum. -/
def MinkowskiSumZ {V : Type*} (S1 S2 : Set (V → ℤ)) : Set (V → ℤ) :=
  {x | ∃ x1 ∈ S1, ∃ x2 ∈ S2, x = x1 + x2}

end DiscreteConvex.IntegralConvexityB
