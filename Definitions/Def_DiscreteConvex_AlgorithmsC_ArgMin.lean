import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of an integer-domain function. -/
def ArgMin (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | ∀ y, g x ≤ g y}

end DiscreteConvex.AlgorithmsC
