import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The price-shifted cost `C[−p](y) = C(y) − ⟨p,y⟩`. -/
def PriceShiftConvex (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) (y : K → ℤ) : WithTop ℝ :=
  C y + ((-(∑ k, p k * (y k : ℝ)) : ℝ) : WithTop ℝ)

end DiscreteConvex.EconomicEquilibriumB
