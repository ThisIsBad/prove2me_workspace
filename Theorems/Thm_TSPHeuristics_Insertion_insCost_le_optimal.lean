import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- (3.12), p. 572: in an insertion method run, every insertion cost is at most OPTIMAL:
`COST(T_i, a_i) ≤ OPTIMAL` for `1 ≤ i < n`. -/
theorem insCost_le_optimal {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    ∀ i : ℕ, 1 ≤ i → i < n → insCost d (T i) (a i) ≤ TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.Insertion
