import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiomLoc
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.136, Theorem 6.4, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Theorem 6.4 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.136). See the item's
`natural_language_statement` for the full statement. -/
theorem local_exchange_iff_exchange {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hdom : ExchangeAxiomB (DomZ f)) :
    MExchangeAxiom f ↔ MExchangeAxiomLoc f := by sorry

end DiscreteConvex.MConvexFunctionsB

