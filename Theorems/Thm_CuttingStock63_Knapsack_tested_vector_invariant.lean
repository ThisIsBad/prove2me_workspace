import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem
import Definitions.Def_CuttingStock63_Knapsack_Method

namespace CuttingStock63.Knapsack

/-- Knapsack Method, paragraph after Step (7), p. 868, in corrected form: on every entry to
Step (3) of every run, (i) for every j, c_j ≤ M_j and M_j is c_j or the objective of a vector
satisfying L_j ≥ λ·(α)_m; and (ii) for the longest stock length L_1, every vector satisfying
L_1 ≥ λ·(α)_m that is lexicographically larger than the vector about to be tested has objective
at most M_1. (Clause (ii) fails for the shorter stock lengths: see the Formalization Note.) -/
theorem tested_vector_invariant {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (hL : StrictAnti L)
    (σ : State m k) (hσ : Reachable l b L c hk σ) (hu : σ.phase = .update) :
    (∀ j : Fin k, c j ≤ σ.M j ∧
        (σ.M j = c j ∨ ∃ a : Fin m → ℕ, Fits l (L j) a ∧ bet b a m = σ.M j)) ∧
      ∀ a' : Fin m → ℕ, toLex σ.a < toLex a' → Fits l (L ⟨0, hk⟩) a' →
        bet b a' m ≤ σ.M ⟨0, hk⟩ := by sorry

end CuttingStock63.Knapsack

