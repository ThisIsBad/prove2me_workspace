import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `v` is the immediate predecessor of `u` in `L`. -/
def ImmediatePred (L : V ≃ Fin (Fintype.card V)) (v u : V) : Prop := (L v).val + 1 = (L u).val

end DiscreteConvex.AlgorithmsB
