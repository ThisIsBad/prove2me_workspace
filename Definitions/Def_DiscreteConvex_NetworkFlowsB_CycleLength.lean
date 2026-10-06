import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The length of a closed walk. -/
def CycleLength {Arc : Type*} (l : Arc → WithTop ℝ) (k : ℕ) (a : Fin (k+1) → Arc) : WithTop ℝ :=
  ∑ i : Fin (k+1), l (a i)

end DiscreteConvex.NetworkFlowsB
