import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ArgMinTop
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_PriceShiftConvex

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The supply set `Sl(p) = arg min Cl[−p]`. -/
def SupplySet (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) : Set (K → ℤ) :=
  ArgMinTop (PriceShiftConvex C p)

end DiscreteConvex.EconomicEquilibriumB
