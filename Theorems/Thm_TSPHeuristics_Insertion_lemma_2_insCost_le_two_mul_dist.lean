import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- Lemma 2, p. 571, (3.3): for a subtour `T`, a node `k` not in `T` and a node `j` in `T`,
`COST(T, k) ≤ 2 · d(k, j)`. -/
theorem lemma_2_insCost_le_two_mul_dist {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : List (Fin n)) (hT : T.Nodup) (k j : Fin n) (hk : k ∉ T) (hj : j ∈ T) :
    insCost d T k ≤ 2 * d k j := by sorry

end TSPHeuristics.Insertion
