import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The negative support of a real vector. -/
noncomputable def SuppNegR' (x : V → ℝ) : Finset V := Finset.univ.filter (fun v => x v < 0)

-- ===== Linear orderings, extreme bases (§10.2.1) =====

end DiscreteConvex.AlgorithmsB
