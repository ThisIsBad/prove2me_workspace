import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic

namespace ServiceParts.StockLevels

theorem fill_rate_differences (lam tbar : ℝ) (hlam : 0 < lam) (htbar : 0 < tbar) (s : ℕ) :
    fdiff (poissonFillRate (lam * tbar)) s = poissonPmf (lam * tbar) s ∧
    fdiff2 (poissonFillRate (lam * tbar)) s
      = poissonPmf (lam * tbar) (s + 1) - poissonPmf (lam * tbar) s ∧
    fdiff2 (poissonFillRate (lam * tbar)) s
      = poissonPmf (lam * tbar) s * (lam * tbar / ((s : ℝ) + 1) - 1) ∧
    ((s : ℝ) + 1 < lam * tbar → 0 < fdiff2 (poissonFillRate (lam * tbar)) s) ∧
    ((¬ ∃ n : ℕ, lam * tbar = n) →
      (fdiff2 (poissonFillRate (lam * tbar)) s ≤ 0 ↔ ⌊lam * tbar⌋₊ ≤ s)) ∧
    ((∃ n : ℕ, lam * tbar = n) →
      (fdiff2 (poissonFillRate (lam * tbar)) s ≤ 0 ↔ lam * tbar - 1 ≤ (s : ℝ))) := by sorry

end ServiceParts.StockLevels

