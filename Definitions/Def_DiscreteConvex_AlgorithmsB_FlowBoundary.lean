import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `∂ϕ(v) = Σ_u ϕ(v,u) - Σ_u ϕ(u,v)`. -/
def FlowBoundary (phi : V → V → ℝ) (v : V) : ℝ := (∑ u, phi v u) - (∑ u, phi u v)

end DiscreteConvex.AlgorithmsB
