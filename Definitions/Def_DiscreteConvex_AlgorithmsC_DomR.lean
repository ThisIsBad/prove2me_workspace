import Mathlib

namespace DiscreteConvex.AlgorithmsC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The effective domain of a real-domain function. -/
def DomR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {x | g x ≠ ⊤}

end DiscreteConvex.AlgorithmsC
