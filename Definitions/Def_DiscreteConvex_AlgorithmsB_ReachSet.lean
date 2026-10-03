import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `R(u)`, the set of vertices reachable from `u` in the digraph `(U,F)`. -/
noncomputable def ReachSet {U : Type*} [Fintype U] [DecidableEq U] (F : U → U → Prop) (u : U) : Finset U :=
  Finset.univ.filter (fun w => Relation.ReflTransGen F u w)

end DiscreteConvex.AlgorithmsB
