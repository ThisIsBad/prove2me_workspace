import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem
import Definitions.Def_CuttingStock63_Knapsack_Method

namespace CuttingStock63.Knapsack

/-- Knapsack Method, Steps (1)–(7) and the paragraph after Step (7), p. 868, in corrected form:
for data sorted as in Step (1), every run of the method from Step (2) is finite, a state other
than the end always has a next step, and at the end every M_j is c_j or attained by a vector
satisfying L_j ≥ λ·(α)_m with c_j ≤ M_j, while M_1 (the longest stock length) is exactly
max(c_1, M̄_1). With one stock length (k = 1) this is the paper's claim in full. -/
theorem knapsack_method_correct {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (l b : Fin m → ℝ)
    (L c : Fin k → ℝ) (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (hL : StrictAnti L) :
    (∀ σ : State m k, Reachable l b L c hk σ → Acc (fun x y => Step l b L c y x) σ) ∧
      (∀ σ : State m k, Reachable l b L c hk σ → σ.phase ≠ .done →
        ∃ σ' : State m k, Step l b L c σ σ') ∧
      (∀ σ : State m k, Reachable l b L c hk σ → σ.phase = .done →
        (∀ j : Fin k, c j ≤ σ.M j ∧
            (σ.M j = c j ∨ ∃ a : Fin m → ℕ, Fits l (L j) a ∧ bet b a m = σ.M j)) ∧
          IsKnapsackMax l b (L ⟨0, hk⟩) (c ⟨0, hk⟩) (σ.M ⟨0, hk⟩)) := by sorry

end CuttingStock63.Knapsack

