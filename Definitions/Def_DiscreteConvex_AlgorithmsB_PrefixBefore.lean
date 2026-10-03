import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The strict prefix before `v` under `L`. -/
def PrefixBefore (L : V ≃ Fin (Fintype.card V)) (v : V) : Finset V :=
  Finset.univ.filter (fun w => L w < L v)

end DiscreteConvex.AlgorithmsB
