import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem
import Definitions.Def_CuttingStock63_Knapsack_Method

namespace CuttingStock63.Knapsack

/-- Knapsack Method, Step (1), p. 867: the vectors tested in Step (3) are generated in
lexicographically decreasing order, and every one after the first satisfies L_1 ≥ λ·(α)_m. -/
theorem tested_vectors_decrease {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i) (hL : StrictAnti L) (σ σ' : State m k)
    (hσ : Reachable l b L c hk σ) (hu : σ.phase = .update)
    (hσσ' : Relation.TransGen (Step l b L c) σ σ') (hu' : σ'.phase = .update) :
    toLex σ'.a < toLex σ.a ∧ Fits l (L ⟨0, hk⟩) σ'.a := by sorry

end CuttingStock63.Knapsack

