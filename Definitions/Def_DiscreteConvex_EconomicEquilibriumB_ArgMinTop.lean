import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The minimizer set of a `WithTop ℝ`-valued function. -/
def ArgMinTop (g : (K → ℤ) → WithTop ℝ) : Set (K → ℤ) := {x | ∀ y, g x ≤ g y}

end DiscreteConvex.EconomicEquilibriumB
