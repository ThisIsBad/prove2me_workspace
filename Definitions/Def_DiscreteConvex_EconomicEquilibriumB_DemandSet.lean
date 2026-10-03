import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ArgMaxBot
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_PriceShift

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The demand set `Dh(p) = arg max (Uh(x) − ⟨p,x⟩)`. -/
def DemandSet (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) : Set (K → ℤ) := ArgMaxBot (PriceShift U p)

end DiscreteConvex.EconomicEquilibriumB
