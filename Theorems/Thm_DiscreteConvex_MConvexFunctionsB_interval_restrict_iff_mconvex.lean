import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_IntervalRestrict
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.144, Proposition 6.14, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.14 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.144). See the item's
`natural_language_statement` for the full statement. -/
theorem interval_restrict_iff_mconvex {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) :
    MExchangeAxiom f ↔
      ∀ a b : V → WithBot (WithTop ℤ), (DomZ (IntervalRestrict f a b)).Nonempty →
        MExchangeAxiom (IntervalRestrict f a b) := by sorry

end DiscreteConvex.MConvexFunctionsB
