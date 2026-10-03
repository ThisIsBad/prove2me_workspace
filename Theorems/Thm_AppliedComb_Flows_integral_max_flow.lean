import Mathlib
import Definitions.Def_AppliedComb_Flows_Network

namespace AppliedComb.Flows

/-- **Theorem 14.1** (Keller & Trotter, *Applied Combinatorics*, 2017 Edition, p. 279). In a
network flow problem in which every edge has integer capacity, there is a maximum flow in which
every edge carries an integer amount of flow: a flow `ϕ` whose value is at least the value of
every flow, with `ϕ(x, y) ∈ ℤ` for every edge `(x, y)`. -/
theorem integral_max_flow {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : ∀ x y, N.adj x y → ∃ n : ℤ, N.cap x y = n) :
    ∃ ϕ : V → V → ℝ, N.IsFlow ϕ ∧
      (∀ ψ : V → V → ℝ, N.IsFlow ψ → N.value ψ ≤ N.value ϕ) ∧
      ∀ x y, N.adj x y → ∃ n : ℤ, ϕ x y = n := by sorry

end AppliedComb.Flows

