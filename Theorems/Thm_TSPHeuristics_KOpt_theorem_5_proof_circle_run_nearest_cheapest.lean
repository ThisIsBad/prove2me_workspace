import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance

namespace TSPHeuristics.KOpt

theorem theorem_5_proof_circle_run_nearest_cheapest (n : ℕ) (hn : 6 ≤ n) :
    TSPHeuristics.Shared.IsInsertionRun (cycDist n) (circleSubtour n) (circleNode n (by omega)) ∧
      TSPHeuristics.Shared.IsNearestRule (cycDist n) (circleSubtour n) (circleNode n (by omega)) ∧
      TSPHeuristics.Shared.IsCheapestRule (cycDist n) (circleSubtour n) (circleNode n (by omega)) := by sorry

end TSPHeuristics.KOpt
