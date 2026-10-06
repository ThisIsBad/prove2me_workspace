import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The negative support for integer vectors. -/
def SuppNeg (x y : K → ℤ) : Finset K := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.EconomicEquilibriumB
