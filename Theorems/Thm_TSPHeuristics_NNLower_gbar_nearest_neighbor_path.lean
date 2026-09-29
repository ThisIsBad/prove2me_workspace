import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- Property b), p. 568: for `i ≥ 1`, the nearest neighbor method started at the start node of
`Ḡ_i` can (with suitable resolution of ties) produce the path `P_i` followed by the edge returning
from the middle node to the start node: the tour that visits the nodes in the order of `P_i` is a
nearest-neighbor tour of `Ḡ_i`. -/
theorem gbar_nearest_neighbor_path (i : ℕ) (hi : 1 ≤ i) :
    ∃ τ : Equiv.Perm (Fin (numNodes i)),
      (∀ k : Fin (numNodes i), (τ k : ℕ) = (pathP i).getD k 0) ∧
      IsNearestNeighborTour (gbar i) τ := by sorry

end TSPHeuristics.NNLower
