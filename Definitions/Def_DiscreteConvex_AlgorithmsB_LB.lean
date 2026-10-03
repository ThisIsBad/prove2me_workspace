import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `ℓ_B(v) = min_{y∈B} y(v)`. -/
noncomputable def LB (B : Set (V → ℤ)) (v : V) : ℤ := sInf ((fun y : V → ℤ => y v) '' B)

end DiscreteConvex.AlgorithmsB
