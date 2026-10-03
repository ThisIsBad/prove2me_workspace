import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_Epi

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.79, Eq. (3.15): convexity of a function via
its epigraph, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `f` is convex iff `epi f` is a convex set (Eq. (3.15)), the equivalent characterization the
book gives to (3.4). -/
def IsConvexF {V : Type*} [Fintype V] (f : (V → ℝ) → EReal) : Prop :=
  Convex ℝ (Epi f)

end DiscreteConvex.IntegralConvexityB
