import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of a `WithTop ℝ`-valued function on any type. -/
def ArgMinOn {W : Type*} (g : W → WithTop ℝ) : Set W := {x | ∀ y, g x ≤ g y}

end DiscreteConvex.MConvexFunctionsC
