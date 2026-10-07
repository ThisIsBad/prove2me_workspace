import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem
import Definitions.Def_CuttingStock63_Knapsack_Method

namespace CuttingStock63.Knapsack

/-- Steps (2) and (7), pp. 867–868: if the prefix (α)_s satisfies cap ≥ λ·(α)_s, the greedy
completion of Steps (2)/(7) is the lexicographically largest extension (α)_m of (α)_s that
satisfies cap ≥ λ·(α)_m. With `s = 0` this is Step (2)'s "lexicographically largest m-vector". -/
theorem greedy_lex_largest {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (cap : ℝ)
    (a : Fin m → ℕ) (s : ℕ) (hs : s ≤ m) (hfit : lam l a s ≤ cap) :
    IsExtension a (greedyFill l cap a s) s ∧ Fits l cap (greedyFill l cap a s) ∧
      ∀ a' : Fin m → ℕ, IsExtension a a' s → Fits l cap a' →
        toLex a' ≤ toLex (greedyFill l cap a s) := by sorry

end CuttingStock63.Knapsack

