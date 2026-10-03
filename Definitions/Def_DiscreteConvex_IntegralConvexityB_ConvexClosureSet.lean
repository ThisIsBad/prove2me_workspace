import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_EmbedZR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, "convex closure"/"convex hull": the real
convex hull of a discrete set of integer vectors, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- The convex hull `S̄ ⊆ Rⱽ` of a discrete set `S ⊆ Zⱽ`. -/
def ConvexClosureSet {V : Type*} (S : Set (V → ℤ)) : Set (V → ℝ) :=
  convexHull ℝ (EmbedZR '' S)

end DiscreteConvex.IntegralConvexityB
