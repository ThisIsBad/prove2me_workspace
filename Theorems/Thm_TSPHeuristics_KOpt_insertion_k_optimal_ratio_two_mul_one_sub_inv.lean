import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion
import Definitions.Def_TSPHeuristics_KOpt_KOptimal

namespace TSPHeuristics.KOpt

theorem insertion_k_optimal_ratio_two_mul_one_sub_inv (n k : ℕ) (hn : 6 ≤ n) (hk : 4 * k ≤ n) :
    ∃ d : Fin n → Fin n → ℝ, TSPHeuristics.Shared.IsTSPDist d ∧ 0 < TSPHeuristics.Shared.optimal d ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsNearestRule d T a ∧
        IsKOptimal d k (T n) ∧ TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsCheapestRule d T a ∧
        IsKOptimal d k (T n) ∧ TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) := by sorry

end TSPHeuristics.KOpt

