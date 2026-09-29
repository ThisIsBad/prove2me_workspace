import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
import Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect

namespace ChvatalPolytopes.Perfect

/-- **Theorem 3.1** (Chvátal 1975, p. 140). For every graph `G = (V, E)`, the following two
conditions are equivalent:
(i) the inequalities `−x_u ≤ 0 (u ∈ V)` and `Σ (x_u : u ∈ W) ≤ 1 (W ∈ C(G))` constitute a
defining linear system of `P(G)`, i.e. their solution set is exactly `P(G) = conv S(G)`;
(ii) `G` is perfect (the paper's α-perfection, `IsPerfect`).
`C(G)` is the set of vertex sets of the **maximal** cliques of `G`. -/
theorem clique_system_defines_iff_perfect {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ W ∈ maximalCliques G, ∑ u ∈ W, x u ≤ 1} = stablePolytope G ↔
      IsPerfect G := by sorry

end ChvatalPolytopes.Perfect

