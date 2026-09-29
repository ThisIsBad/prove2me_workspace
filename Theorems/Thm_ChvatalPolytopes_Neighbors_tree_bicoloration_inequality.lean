import Mathlib
import Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope
import Definitions.Def_ChvatalPolytopes_Neighbors_IsBicoloration

namespace ChvatalPolytopes.Neighbors

/-- **Lemma 6.1** (Chvátal 1975, p. 149). Let `T = (V, E)` be a tree with a bicoloration
`V = B ∪ R`. Then there are nonnegative integers `c_u` (`u ∈ V`) and `m` such that
`Σ (c_u x_u : u ∈ V) ≤ m` for all `(x_u : u ∈ V) ∈ S(T)`, with equality if and only if `x` is
the incidence vector of `B` or the incidence vector of `R`. -/
theorem tree_bicoloration_inequality {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (B R : Finset V) (hBR : IsBicoloration T B R) :
    ∃ (c : V → ℕ) (m : ℕ), ∀ x ∈ stableVectors T,
      (∑ u, (c u : ℝ) * x u ≤ (m : ℝ)) ∧
      (∑ u, (c u : ℝ) * x u = (m : ℝ) ↔ x = incidenceVector B ∨ x = incidenceVector R) := by sorry

end ChvatalPolytopes.Neighbors
