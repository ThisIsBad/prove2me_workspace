import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The positive support of a real vector. -/
noncomputable def SuppPosR' (x : V → ℝ) : Finset V := Finset.univ.filter (fun v => 0 < x v)

end DiscreteConvex.AlgorithmsB
