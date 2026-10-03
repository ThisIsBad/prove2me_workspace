import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The positive support of `x - y`, real-vector version. -/
noncomputable def SuppPosR (x y : V → ℝ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.AlgorithmsC
