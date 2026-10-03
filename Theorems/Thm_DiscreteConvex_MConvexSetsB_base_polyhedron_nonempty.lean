import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.105, Proposition 4.4, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.4 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.105). See the item's
`natural_language_statement` for the full statement. -/
theorem base_polyhedron_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) :
    (BasePolyhedron ρ).Nonempty := by sorry

end DiscreteConvex.MConvexSetsB
