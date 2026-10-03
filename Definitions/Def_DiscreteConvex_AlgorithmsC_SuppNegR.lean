import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The negative support of `x - y`, real-vector version. -/
noncomputable def SuppNegR (x y : V → ℝ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.AlgorithmsC
