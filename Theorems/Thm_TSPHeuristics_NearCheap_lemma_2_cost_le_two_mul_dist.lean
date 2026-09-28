import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion

namespace TSPHeuristics.NearCheap

theorem lemma_2_cost_le_two_mul_dist {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : List (Fin n)) (hT : T.Nodup) (hTne : T ≠ []) (k j : Fin n) (hk : k ∉ T) (hj : j ∈ T) :
    TSPHeuristics.Shared.insCost d T k ≤ 2 * d k j := by sorry

end TSPHeuristics.NearCheap

