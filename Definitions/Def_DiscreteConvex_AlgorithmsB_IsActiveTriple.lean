import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_ImmediatePred

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `(i,u,v)` is an active triple: `u∈W`, `v∉W`, and `v` immediately precedes `u` in `Lᵢ`. -/
def IsActiveTriple {ι : Type*} (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (W : Finset V)
    (i : ι) (u v : V) : Prop :=
  i ∈ I ∧ u ∈ W ∧ v ∉ W ∧ ImmediatePred (L i) v u

end DiscreteConvex.AlgorithmsB
