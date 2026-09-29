import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- p. 569: for `i ≥ 3` (i.e. `m = i + 1 > 3`), the ratio `(L_i + l_i − 1)/n` of `Ḡ_i`, with
`n = 2^(i+1) − 1`, exceeds the bound `(1/3) lg(n + 1) + 4/9` of Theorem 2 (ratio multiplied
out by `n > 0`). -/
theorem ratio_gt_bound (i : ℕ) (hi : 3 ≤ i) :
    (1 / 3 * Real.logb 2 ((numNodes i : ℝ) + 1) + 4 / 9) * (numNodes i : ℝ) <
      pathLength i + ell i - 1 := by sorry

end TSPHeuristics.NNLower
