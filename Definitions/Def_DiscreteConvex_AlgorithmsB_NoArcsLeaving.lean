import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- No arc of `active` leaves `W`. -/
def NoArcsLeaving (active : V → V → Prop) (W : Finset V) : Prop :=
  ∀ u ∈ W, ∀ v, active u v → v ∈ W

end DiscreteConvex.AlgorithmsB
