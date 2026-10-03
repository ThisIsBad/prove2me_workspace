import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DiscreteConvexUnivariate
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_UnivToFunc
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ConservationLift
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuasiSeparable


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.140, Proposition 6.9, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.9 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.140). See the item's
`natural_language_statement` for the full statement. -/
theorem univariate_convex_examples (psi : ℤ → WithTop ℝ) (hpsi : DiscreteConvexUnivariate psi) :
    MNaturalConvex (UnivToFunc psi) ∧
    MExchangeAxiom (ConservationLift psi) ∧
    (∀ {W : Type*} [Fintype W] [DecidableEq W] (f0 : ℤ → WithTop ℝ) (fi : W → ℤ → WithTop ℝ),
      DiscreteConvexUnivariate f0 → (∀ v, DiscreteConvexUnivariate (fi v)) →
      MNaturalConvex (QuasiSeparable f0 fi)) := by sorry

end DiscreteConvex.MConvexFunctionsB
