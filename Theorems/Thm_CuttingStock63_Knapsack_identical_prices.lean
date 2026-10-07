import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem

namespace CuttingStock63.Knapsack

/-- Identical Prices, paragraph "Clearly, identical prices …", p. 869: if l_i < l_j and b_i = b_j, then every vector
satisfying the constraint of (1) can be replaced by one with a_j = 0, still satisfying the
constraint, with the same objective (substitute l_i for every piece of length l_j). So the
maximum of (1) does not change when the variable a_j is dropped. -/
theorem identical_prices {m : ℕ} (l b : Fin m → ℝ) (L : ℝ) (i j : Fin m) (hij : i ≠ j)
    (hlt : l i < l j) (hbeq : b i = b j) (a : Fin m → ℕ) (ha : Fits l L a) :
    ∃ a' : Fin m → ℕ, Fits l L a' ∧ a' j = 0 ∧ bet b a' m = bet b a m := by sorry

end CuttingStock63.Knapsack

