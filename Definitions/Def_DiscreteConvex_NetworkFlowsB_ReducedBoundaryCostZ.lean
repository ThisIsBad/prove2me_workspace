import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The reduced boundary cost, integer domain, real potential. -/
def ReducedBoundaryCostZ (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (x : V → ℤ) : WithTop ℝ :=
  f x - ((∑ v, p v * (x v : ℝ) : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB
