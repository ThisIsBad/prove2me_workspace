import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntPts


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.108, Theorem 4.12, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Theorem 4.12 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.108). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_hole_free {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ))
    (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) :
    IntEmbed B = convexHull ℝ (IntEmbed B) ∩ IntPts := by sorry

end DiscreteConvex.MConvexSetsB

