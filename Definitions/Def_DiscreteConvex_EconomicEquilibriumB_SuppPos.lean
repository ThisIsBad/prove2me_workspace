import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The positive support for integer vectors. -/
def SuppPos (x y : K → ℤ) : Finset K := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.EconomicEquilibriumB
