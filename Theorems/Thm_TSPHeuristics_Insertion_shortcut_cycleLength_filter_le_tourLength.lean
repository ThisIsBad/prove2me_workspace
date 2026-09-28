import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- (2.2), p. 565, in the general form the argument proves: visiting any subset `H` of the
nodes in the order in which a tour `τ` visits them gives a closed tour on `H` no longer than `τ`
(the triangle inequality shortcuts the skipped nodes). -/
theorem shortcut_cycleLength_filter_le_tourLength {n : ℕ} (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (τ : Equiv.Perm (Fin n)) (H : Finset (Fin n)) :
    TSPHeuristics.Shared.cycleLength d ((List.ofFn τ).filter (fun i => decide (i ∈ H))) ≤ TSPHeuristics.Shared.tourLength d τ := by sorry

end TSPHeuristics.Insertion
