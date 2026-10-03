import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The maximizer set of a `WithBot ℝ`-valued function. -/
def ArgMaxBot (g : (K → ℤ) → WithBot ℝ) : Set (K → ℤ) := {x | ∀ y, g y ≤ g x}

end DiscreteConvex.EconomicEquilibriumB
