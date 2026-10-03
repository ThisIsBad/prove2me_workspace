import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101 (citing Eq. (1.19)): the negative
support of a difference of integer vectors, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The negative support `supp⁻(x - y) = \{v : x(v) < y(v)\}`. -/
def SuppNeg {V : Type*} (x y : V → ℤ) : Set V :=
  {v | x v < y v}

end DiscreteConvex.MConvexSetsB
