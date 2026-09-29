import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation
import Definitions.Def_EdmondsKarp_MaxCapacity_Run

namespace EdmondsKarp.MaxCapacity

/-- Proof of Theorem 2, p. 254: for a network `N` with integer capacities, a set of nodes `X` with
`s ∈ X`, `t ∉ X`, and any flow `f`: `c(X, X̄) ≥ f(X, X̄) − f(X̄, X) = f(t, s)`. -/
theorem cut_bound {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (X : Finset V) (hs : N.s ∈ X) (ht : N.t ∉ X)
    (f : V → V → ℝ) (hf : IsFlow N f) :
    cutFlowOut N f X - cutFlowIn N f X = f N.t N.s ∧
      cutFlowOut N f X - cutFlowIn N f X ≤ cutCap N X := by sorry

end EdmondsKarp.MaxCapacity
