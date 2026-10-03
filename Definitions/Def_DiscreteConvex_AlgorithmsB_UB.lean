import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `u_B(v) = max_{y∈B} y(v)`. -/
noncomputable def UB (B : Set (V → ℤ)) (v : V) : ℤ := sSup ((fun y : V → ℤ => y v) '' B)

end DiscreteConvex.AlgorithmsB
