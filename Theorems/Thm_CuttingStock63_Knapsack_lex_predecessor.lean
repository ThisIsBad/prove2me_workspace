import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem

namespace CuttingStock63.Knapsack

/-- Step (4), p. 867: let (α)_m satisfy cap ≥ λ·(α)_m and let `i` (the paper's s, 0-based) be the
largest index with a_i ≠ 0. Among the m-vectors satisfying the length constraint and
lexicographically smaller than (α)_m there is a lexicographically largest one, and every such
largest vector is an extension of (α¹)_s, which differs from (α)_s only in having a_s − 1 as its
s-th coefficient. -/
theorem lex_predecessor {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (cap : ℝ)
    (a : Fin m → ℕ) (hfit : Fits l cap a) (i : Fin m) (hi : a i ≠ 0)
    (hmax : ∀ i' : Fin m, i < i' → a i' = 0) :
    (∃ g : Fin m → ℕ, Fits l cap g ∧ toLex g < toLex a ∧
        ∀ a' : Fin m → ℕ, Fits l cap a' → toLex a' < toLex a → toLex a' ≤ toLex g) ∧
      ∀ g : Fin m → ℕ, Fits l cap g → toLex g < toLex a →
        (∀ a' : Fin m → ℕ, Fits l cap a' → toLex a' < toLex a → toLex a' ≤ toLex g) →
          IsExtension (decrAt a (i.val + 1)) g (i.val + 1) := by sorry

end CuttingStock63.Knapsack

