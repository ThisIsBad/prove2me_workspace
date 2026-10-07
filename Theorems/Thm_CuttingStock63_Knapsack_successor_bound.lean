import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem

namespace CuttingStock63.Knapsack

/-- Knapsack Method, paragraph before Step (5), p. 868 (the successor of Step (6)), in corrected
form: if the inequality of the test of Step (5) fails for a stock length L with current value M at
the prefix (α)_s, that is (L − λ·(α)_s) b_{s+1} ≤ (M − β·(α)_s) l_{s+1}, then no vector a' that
agrees with (α)_s in its first s − 1 coefficients, has a'_s ≤ a_s and satisfies L ≥ λ·(α')_m
improves M. Hence nothing between (α)_s and the successor computed in Step (6) can improve M. -/
theorem successor_bound {m : ℕ} (l b : Fin m → ℝ) (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (L M : ℝ) (a : Fin m → ℕ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsm : s ≤ m)
    (hfail : (L - lam l a s) * nextB b s ≤ (M - bet b a s) * nextL l s)
    (a' : Fin m → ℕ) (hpre : ∀ i : Fin m, i.val + 1 < s → a' i = a i)
    (hlast : ∀ i : Fin m, i.val + 1 = s → a' i ≤ a i) (hfit : Fits l L a') :
    bet b a' m ≤ M := by sorry

end CuttingStock63.Knapsack

