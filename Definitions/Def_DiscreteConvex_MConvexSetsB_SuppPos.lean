import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101 (citing Eq. (1.19)): the positive
support of a difference of integer vectors, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The positive support `supp⁺(x - y) = \{v : x(v) > y(v)\}`. -/
def SuppPos {V : Type*} (x y : V → ℤ) : Set V :=
  {v | y v < x v}

end DiscreteConvex.MConvexSetsB
