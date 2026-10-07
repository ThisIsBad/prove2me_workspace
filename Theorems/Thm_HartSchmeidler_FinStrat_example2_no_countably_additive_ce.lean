import Definitions.Def_HartSchmeidler_FinStrat_Peleg

namespace HartSchmeidler.FinStrat

open MeasureTheory

/-- Example 2, p. 22: the modified Peleg game has no countably additive
correlated equilibrium on the product σ-algebra. -/
theorem example2_no_countably_additive_ce :
    ¬ ∃ μ : Measure (PNat → Fin 2), IsCorrelatedEq peleg2Payoff μ := by sorry

end HartSchmeidler.FinStrat

