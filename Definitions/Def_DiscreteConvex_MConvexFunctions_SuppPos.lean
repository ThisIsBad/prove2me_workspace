import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133, citing Eq. (1.19): the positive support
of a difference of integer vectors, in `DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- The positive support `supp⁺(x - y) = \{v : x(v) > y(v)\}`, as a `Finset` (`V` is finite). -/
def SuppPos {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.MConvexFunctions
