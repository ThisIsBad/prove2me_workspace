import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting

namespace ChinesePostman.Matching


/-- §3, p. 92: overlapping shortest paths of matching edges can be uncrossed. -/
theorem exists_edge_disjoint_shortest_paths
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Connected G) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (d : V → V → ℝ) (hd : ∀ i j, IsShortestPathLength G c i j (d i j))
    (f : V → V) (hf : IsOddPerfectMatching G f) :
    ∃ f' : V → V, IsOddPerfectMatching G f' ∧
      matchingLength G d f' ≤ matchingLength G d f ∧
      ∃ P : V → List V × List E, MatchingPaths G f' P ∧
        ∀ v ∈ oddNodes G, walkLength c (P v).2 = d v (f' v) := by sorry
end ChinesePostman.Matching

