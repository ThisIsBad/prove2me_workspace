import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A closed walk `a : Fin (k+1) → Arc` in a digraph `(tail,head)`. -/
def IsCycle {Arc W : Type*} (tail head : Arc → W) (k : ℕ) (a : Fin (k+1) → Arc) : Prop :=
  ∀ i : Fin (k+1), head (a i) = tail (a (i+1))

end DiscreteConvex.NetworkFlowsB
