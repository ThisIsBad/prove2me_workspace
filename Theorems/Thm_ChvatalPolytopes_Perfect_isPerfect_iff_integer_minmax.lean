import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
import Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect

namespace ChvatalPolytopes.Perfect

/-- **Condition (iii) ⇔ (ii)** (Chvátal 1975, §3, proof of Theorem 3.1, p. 141). A graph `G` is
perfect if and only if (iii): for every integer-valued vector `c = (c_u : u ∈ V)`, the maximum of
`{cx : x ∈ S(G)}` is equal to the minimum of
`{Σ (λ_W : W ∈ C(G)) : λ_W ≥ 0 for all W ∈ C(G) and Σ (λ_W : u ∈ W ∈ C(G)) ≥ c_u for all u ∈ V}`.

"max = min" is spelled out: some `m` is the maximum over `S(G)`, is attained by a feasible
nonnegative real `λ`, and is at most the objective of every feasible `λ`. Weights are
`λ : Finset V → ℝ`, read only on `C(G) = maximalCliques G` (maximal cliques). -/
theorem isPerfect_iff_integer_minmax {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    IsPerfect G ↔
      ∀ c : V → ℤ, ∃ m : ℝ, IsStableMax G (fun u => (c u : ℝ)) m ∧
        (∃ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, 0 ≤ lam W) ∧
          (∀ u, (c u : ℝ) ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) ∧
          ∑ W ∈ maximalCliques G, lam W = m) ∧
        (∀ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, 0 ≤ lam W) →
          (∀ u, (c u : ℝ) ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) →
          m ≤ ∑ W ∈ maximalCliques G, lam W) := by sorry

end ChvatalPolytopes.Perfect

