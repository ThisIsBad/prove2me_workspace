import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133, citing Eq. (1.19): the negative support
of a difference of integer vectors, in `DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- The negative support `supp⁻(x - y) = \{v : x(v) < y(v)\}`, as a `Finset` (`V` is finite). -/
def SuppNeg {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.MConvexFunctions
