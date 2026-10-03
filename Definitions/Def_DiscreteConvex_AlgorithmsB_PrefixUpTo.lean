import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `V_h = {v ∈ V | v ⪯_L v_h}`, the prefix up to and including `v` under `L`. -/
def PrefixUpTo (L : V ≃ Fin (Fintype.card V)) (v : V) : Finset V :=
  Finset.univ.filter (fun w => L w ≤ L v)

end DiscreteConvex.AlgorithmsB
