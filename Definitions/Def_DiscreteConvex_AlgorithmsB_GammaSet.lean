import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `Γ(Y) = ⋃_{u∈Y} Γ(u)`. -/
def GammaSet {U : Type*} [DecidableEq U] (Gamma : U → Finset V) (Y : Finset U) : Finset V :=
  Y.biUnion Gamma

end DiscreteConvex.AlgorithmsB
