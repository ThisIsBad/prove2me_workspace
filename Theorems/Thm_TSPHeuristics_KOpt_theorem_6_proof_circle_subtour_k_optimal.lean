import Mathlib
import Definitions.Def_TSPHeuristics_KOpt_KOptimal
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance

namespace TSPHeuristics.KOpt

theorem theorem_6_proof_circle_subtour_k_optimal (n k : ℕ) (hn : 6 ≤ n) (hk : 4 * k ≤ n) :
    IsKOptimal (cycDist n) k (circleSubtour n n) := by sorry

end TSPHeuristics.KOpt
