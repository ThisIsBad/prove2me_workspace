import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133, citing Eq. (1.19), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The negative support `supp⁻(x - y)`, as a `Finset` (`V` is finite). -/
def SuppNeg {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.MConvexFunctionsB
