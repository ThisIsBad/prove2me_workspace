import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of a real-valued function. -/
def DomR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {p | g p ≠ ⊤}

end DiscreteConvex.LConvexFunctionsD
