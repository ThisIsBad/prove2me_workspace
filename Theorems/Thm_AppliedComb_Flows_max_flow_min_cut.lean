import Mathlib
import Definitions.Def_AppliedComb_Flows_Network

namespace AppliedComb.Flows

/-- **Theorem 13.10 (The Max Flow–Min Cut Theorem)** (Keller & Trotter, *Applied Combinatorics*,
2017 Edition, p. 268). Let `N` be a network. There is a number `v₀` which is the maximum value
of a flow in `N` (it is the value of some flow, and no flow has larger value) and which is also
the minimum capacity of a cut of `N` (it is the capacity of some cut, and no cut has smaller
capacity). In particular the maximum value of a flow exists, the minimum capacity of a cut exists,
and they are equal. -/
theorem max_flow_min_cut {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) :
    ∃ v₀ : ℝ,
      IsGreatest {v : ℝ | ∃ ϕ : V → V → ℝ, N.IsFlow ϕ ∧ N.value ϕ = v} v₀ ∧
      IsLeast {c : ℝ | ∃ L : Finset V, N.IsCut L ∧ N.cutCapacity L = c} v₀ := by sorry

end AppliedComb.Flows

