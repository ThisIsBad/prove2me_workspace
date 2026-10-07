import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem

namespace CuttingStock63.Knapsack

/-- Knapsack Method, paragraph before Step (5), p. 867: with the variables ordered by density
b_1/l_1 ≥ ⋯ ≥ b_m/l_m (and the slack item a_{m+1}, b_{m+1} = 0, l_{m+1} = 1, last), every
extension (α)_m of (α)_s with L ≥ λ·(α)_m has β·(α)_m ≤ β·(α)_s + b_{s+1}(L − λ·(α)_s)/l_{s+1}.
So β·(α)_s + b_{s+1}(L_j − λ·(α)_s)/l_{s+1} > M_j is necessary for an extension to improve M_j. -/
theorem relaxation_bound {m : ℕ} (l b : Fin m → ℝ) (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (L : ℝ) (a : Fin m → ℕ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsm : s ≤ m) (a' : Fin m → ℕ) (hext : IsExtension a a' s)
    (hfit : Fits l L a') :
    bet b a' m ≤ bet b a s + nextB b s * (L - lam l a s) / nextL l s := by sorry

end CuttingStock63.Knapsack

