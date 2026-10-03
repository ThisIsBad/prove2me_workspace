import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of `g : Zⱽ → R ∪ {+∞}`. -/
def DomZ (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {p | g p ≠ ⊤}

end DiscreteConvex.LConvexFunctionsD
