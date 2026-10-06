import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The reduced boundary cost `f[−p](x) = f(x) − Σ p(v)x(v)`. -/
def ReducedBoundaryCost (f : (V → ℝ) → WithTop ℝ) (p : V → ℝ) (x : V → ℝ) : WithTop ℝ :=
  f x - ((∑ v, p v * x v : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB
