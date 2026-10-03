import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `u ≺_L v`: `u` precedes `v` in the ordering `L` (Eq. (10.14)). -/
def PrecedesIn (L : V ≃ Fin (Fintype.card V)) (u v : V) : Prop := L u < L v

end DiscreteConvex.AlgorithmsB
