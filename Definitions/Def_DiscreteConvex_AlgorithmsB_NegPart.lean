import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `x⁻(v) = min(0,x(v))`. -/
def NegPart (x : V → ℝ) (v : V) : ℝ := min 0 (x v)

end DiscreteConvex.AlgorithmsB
