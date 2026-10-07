import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting

namespace ChinesePostman.Matching


/-- §3, p. 93: the support contains disjoint paths pairing all odd nodes;
even-degree tours may remain outside those paths. -/
theorem zero_one_parity_solution_decomposes
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℕ) (hx : IsParitySolution G x)
    (hx01 : ∀ e, x e ≤ 1) :
    ∃ f : V → V, IsOddPerfectMatching G f ∧
      ∃ P : V → List V × List E, MatchingPaths G f P ∧
        ∀ v ∈ oddNodes G, ∀ e ∈ (P v).2, x e = 1 := by sorry
end ChinesePostman.Matching

