import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- p. 568: for every `i ≥ 1`, the shortest-path distance of `G_i` makes `Ḡ_i` a traveling
salesman graph (symmetric, nonnegative, zero on the diagonal, triangle inequality). -/
theorem gbar_isTSPDist (i : ℕ) (hi : 1 ≤ i) : IsTSPDist (gbar i) := by sorry

end TSPHeuristics.NNLower
