import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Membership in the arc set `Aϕ = {(u,v) | ϕ(u,v)=0}` of Eq. (10.22). -/
def AphiActive (phi : V → V → ℝ) (u v : V) : Prop := u ≠ v ∧ phi u v = 0

end DiscreteConvex.AlgorithmsB
