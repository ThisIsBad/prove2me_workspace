import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of an integer-domain function. -/
def ArgMin (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | ∀ y, f x ≤ f y}

end DiscreteConvex.ConjugacyDualityC
