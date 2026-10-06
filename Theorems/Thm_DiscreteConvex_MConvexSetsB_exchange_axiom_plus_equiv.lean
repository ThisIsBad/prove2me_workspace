import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomBPlus


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101, Proposition 4.2, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.2 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.101). See the item's
`natural_language_statement` for the full statement. -/
theorem exchange_axiom_plus_equiv {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ)) :
    ExchangeAxiomB B ↔ ExchangeAxiomBPlus B := by sorry

end DiscreteConvex.MConvexSetsB

