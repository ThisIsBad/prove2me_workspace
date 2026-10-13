import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegralPolyhedron


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.107, Proposition 4.6, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.6 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.107). See the item's
`natural_language_statement` for the full statement. -/
theorem base_polyhedron_integral {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (hInt : IsIntegerValued ρ) :
    IsIntegralPolyhedron (BasePolyhedron ρ) := by sorry

end DiscreteConvex.MConvexSetsB

