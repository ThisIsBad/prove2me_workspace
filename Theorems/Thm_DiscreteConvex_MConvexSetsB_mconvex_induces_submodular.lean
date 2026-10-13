import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_InducedRho
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.108-109, Proposition 4.13, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.13 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.108-109). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_induces_submodular {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ))
    (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) :
    SubmodularSetFunction (InducedRho B) ∧ IsIntegerValued (InducedRho B) ∧
      convexHull ℝ (IntEmbed B) = BasePolyhedron (InducedRho B) := by sorry

end DiscreteConvex.MConvexSetsB

