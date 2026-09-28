import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion

namespace TSPHeuristics.NearCheap

theorem eq_3_7_insert_eq_sum_cost {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : TSPHeuristics.Shared.IsInsertionRun d T a) :
    TSPHeuristics.Shared.cycleLength d (T n) = ∑ i ∈ Finset.Ico 1 n, TSPHeuristics.Shared.insCost d (T i) (a i) := by sorry

end TSPHeuristics.NearCheap

