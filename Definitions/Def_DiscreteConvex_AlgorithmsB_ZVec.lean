import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_FlowBoundary

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `z = x + ∂ϕ`. -/
def ZVec (x : V → ℝ) (phi : V → V → ℝ) (v : V) : ℝ := x v + FlowBoundary phi v

end DiscreteConvex.AlgorithmsB
