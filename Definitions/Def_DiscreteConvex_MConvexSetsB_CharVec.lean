import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101: the characteristic vector `χ_u` of a
single ground-set element, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The characteristic vector `χ_u ∈ Zⱽ` of `u ∈ V`: `1` at `u`, `0` elsewhere. -/
def CharVec {V : Type*} [DecidableEq V] (u : V) : V → ℤ :=
  fun v => if v = u then 1 else 0

end DiscreteConvex.MConvexSetsB
