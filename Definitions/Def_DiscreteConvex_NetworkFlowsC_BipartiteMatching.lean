import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `M` is a perfect matching between `Vp` and `Vn`. -/
def BipartiteMatching (Vp Vn : Finset V) (M : Finset (V × V)) : Prop :=
  (∀ p ∈ M, p.1 ∈ Vp ∧ p.2 ∈ Vn) ∧
  (∀ u ∈ Vp, ∃! v, (u, v) ∈ M) ∧ (∀ v ∈ Vn, ∃! u, (u, v) ∈ M)

end DiscreteConvex.NetworkFlowsC
