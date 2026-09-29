import Mathlib
import Definitions.Def_TSPHeuristics_KOpt_KOptimal

namespace TSPHeuristics.KOpt

theorem theorem_6_k_optimal_ratio_two_mul_one_sub_inv (n : ℕ) (hn : 8 ≤ n) :
    ∃ d : Fin n → Fin n → ℝ, TSPHeuristics.Shared.IsTSPDist d ∧ 0 < TSPHeuristics.Shared.optimal d ∧
      ∃ τ : Equiv.Perm (Fin n), (∀ k : ℕ, 4 * k ≤ n → IsKOptimalTour d k τ) ∧
        TSPHeuristics.Shared.tourLength d τ = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.KOpt
