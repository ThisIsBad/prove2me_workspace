import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The minimizer set of a univariate real function. -/
def ArgMinArc (g : ℝ → WithTop ℝ) : Set ℝ := {t | ∀ s, g t ≤ g s}

end DiscreteConvex.NetworkFlowsB
