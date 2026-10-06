import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The singleton-indicator boundary cost of Eq. (9.11): `f = δ_{x}`. -/
noncomputable def BoundaryCostMCFP0 (x : V → ℝ) (y : V → ℝ) : WithTop ℝ := if y = x then 0 else ⊤

end DiscreteConvex.NetworkFlowsB
