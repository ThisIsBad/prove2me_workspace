import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The boundary of an integer flow. -/
def BoundaryZ (tail head : A → V) (xi : A → ℤ) (v : V) : ℤ :=
  (∑ a ∈ Finset.univ.filter (fun a => tail a = v), xi a) -
    (∑ a ∈ Finset.univ.filter (fun a => head a = v), xi a)

end DiscreteConvex.NetworkFlowsB
