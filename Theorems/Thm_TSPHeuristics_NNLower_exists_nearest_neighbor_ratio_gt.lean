import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel

namespace TSPHeuristics.NNLower

/-- Theorem 2 (Rosenkrantz–Stearns–Lewis 1977, p. 566): for each `m > 3` there is a traveling
salesman graph with `n = 2^m − 1` nodes and a run of the nearest neighbor algorithm on it whose
tour length NEARNEIBER satisfies `NEARNEIBER / OPTIMAL > (1/3) lg(n + 1) + 4/9`
(ratio multiplied out; `OPTIMAL > 0` is the paper's (1.1)). -/
theorem exists_nearest_neighbor_ratio_gt (m : ℕ) (hm : 3 < m) :
    ∃ d : Fin (2 ^ m - 1) → Fin (2 ^ m - 1) → ℝ, IsTSPDist d ∧ 0 < optimal d ∧
      ∃ τ : Equiv.Perm (Fin (2 ^ m - 1)), IsNearestNeighborTour d τ ∧
        (1 / 3 * Real.logb 2 (((2 ^ m - 1 : ℕ) : ℝ) + 1) + 4 / 9) * optimal d < tourLength d τ := by sorry

end TSPHeuristics.NNLower
