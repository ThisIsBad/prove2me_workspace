import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.115, Theorem 4.22, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Theorem 4.22 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.115). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_intersection_hull {V : Type*} [Fintype V] [DecidableEq V] (B1 B2 : Set (V → ℤ))
    (hExc1 : ExchangeAxiomB B1) (hExc2 : ExchangeAxiomB B2) (hB1ne : B1.Nonempty)
    (hB2ne : B2.Nonempty) :
    convexHull ℝ (IntEmbed (B1 ∩ B2)) = convexHull ℝ (IntEmbed B1) ∩ convexHull ℝ (IntEmbed B2) := by sorry

end DiscreteConvex.MConvexSetsB

