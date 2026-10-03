import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The minimizer set of a univariate integer function. -/
def ArgMinArcZ (g : ℤ → WithTop ℝ) : Set ℤ := {t | ∀ s, g t ≤ g s}

end DiscreteConvex.NetworkFlowsB
