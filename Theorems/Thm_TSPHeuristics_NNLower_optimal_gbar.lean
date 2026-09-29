import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- p. 568: for `i ≥ 1`, `Ḡ_i` has an optimal tour whose length equals its number of nodes
`n = 2^(i+1) − 1` (the left-to-right tour, all of whose edges have weight one). -/
theorem optimal_gbar (i : ℕ) (hi : 1 ≤ i) :
    optimal (gbar i) = (2 : ℝ) ^ (i + 1) - 1 := by sorry

end TSPHeuristics.NNLower
