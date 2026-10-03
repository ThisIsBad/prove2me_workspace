import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133-135, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The characteristic vector `χ_u ∈ Zⱽ` of `u ∈ V`. -/
def CharVec {V : Type*} [DecidableEq V] (u : V) : V → ℤ := fun v => if v = u then 1 else 0

end DiscreteConvex.MConvexFunctionsB
