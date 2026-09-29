import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion

namespace TSPHeuristics.KOpt

theorem theorem_5_insertion_ratio_two_mul_one_sub_inv (n : ℕ) (hn : 6 ≤ n) :
    ∃ d : Fin n → Fin n → ℝ, TSPHeuristics.Shared.IsTSPDist d ∧ 0 < TSPHeuristics.Shared.optimal d ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsNearestRule d T a ∧
        TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsCheapestRule d T a ∧
        TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) := by sorry

end TSPHeuristics.KOpt
