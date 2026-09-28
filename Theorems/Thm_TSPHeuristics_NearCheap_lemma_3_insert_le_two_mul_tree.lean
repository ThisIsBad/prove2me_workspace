import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion
import Definitions.Def_TSPHeuristics_NearCheap_SpanningTree

open Classical

namespace TSPHeuristics.NearCheap

theorem lemma_3_insert_le_two_mul_tree {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : TSPHeuristics.Shared.IsInsertionRun d T a)
    (h45 : ∀ i, 1 ≤ i → i < n → ∀ p ∈ T i, ∀ q, q ∉ T i →
      TSPHeuristics.Shared.insCost d (T i) (a i) ≤ 2 * d p q)
    (M : SimpleGraph (Fin n)) (hM : M.IsTree) :
    TSPHeuristics.Shared.cycleLength d (T n) ≤ 2 * treeWeight d M := by sorry

end TSPHeuristics.NearCheap

