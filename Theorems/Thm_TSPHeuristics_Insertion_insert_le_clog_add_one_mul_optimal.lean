import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- Theorem 3, (3.6), p. 571: for a traveling salesman graph with `n` nodes, every tour
produced by an insertion method (any choice of the inserted nodes, any minimizing insertion
position) has length `INSERT ≤ (⌈lg n⌉ + 1) · OPTIMAL`. -/
theorem insert_le_clog_add_one_mul_optimal {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    TSPHeuristics.Shared.cycleLength d (T n) ≤ ((Nat.clog 2 n : ℝ) + 1) * TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.Insertion

