import Mathlib
import Definitions.Def_TSPHeuristics_NearCheap_SpanningTree

open Classical

namespace TSPHeuristics.NearCheap

theorem eq_4_11_tree_le_one_sub_inv_optimal {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) :
    ∃ M : SimpleGraph (Fin n), M.IsTree ∧
      treeWeight d M ≤ (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.NearCheap

