import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion

namespace TSPHeuristics.NearCheap

theorem insertion_le_two_mul_one_sub_inv_optimal {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : TSPHeuristics.Shared.IsInsertionRun d T a)
    (hrule : TSPHeuristics.Shared.IsNearestRule d T a ∨ TSPHeuristics.Shared.IsCheapestRule d T a) :
    TSPHeuristics.Shared.cycleLength d (T n) ≤ 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.NearCheap

