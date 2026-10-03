import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The price-shifted utility `U[−p](x) = U(x) − ⟨p,x⟩`. -/
def PriceShift (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) (x : K → ℤ) : WithBot ℝ :=
  U x + ((-(∑ k, p k * (x k : ℝ)) : ℝ) : WithBot ℝ)

end DiscreteConvex.EconomicEquilibriumB
