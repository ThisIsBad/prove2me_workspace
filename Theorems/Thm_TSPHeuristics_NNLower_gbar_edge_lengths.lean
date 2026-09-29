import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_ShortestPathMetric
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- Property a), p. 568: for `i ≥ 1`, every edge of `G_i` has the same length in `Ḡ_i` as in
`G_i`, i.e. each edge `(a, b, w)` of `G_i` is a shortest path: `d(a, b) = w`. -/
theorem gbar_edge_lengths (i : ℕ) (hi : 1 ≤ i) :
    ∀ e ∈ edgesG i, spDist (edgesG i) e.1 e.2.1 = e.2.2 := by sorry

end TSPHeuristics.NNLower
