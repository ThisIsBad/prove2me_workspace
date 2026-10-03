import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of an integer-domain function. -/
def DomZ (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | g x ≠ ⊤}

end DiscreteConvex.AlgorithmsC
