import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, p. 67 (the two derivative displays and "Hence, …").
Let `q2sel` select a supply chain optimal period-2 order `q_2(q_1, ξ)`, which the retailer orders
and the supplier fills. For the supplier's period-1 profit `Π_1(x|q_1)` as a function of her
period-1 production `x`:
1. for `x ≥ q_1`, `x > 0`, with `ξ(x)` solving (26) at `x`, the right derivative is
   `−c_1 + c_2(1 − G(ξ(x)))`, and it is a two-sided derivative when `x > q_1`;
2. at a supply chain optimal `q_1° > 0` with `ξ(q_1°)` solving (26),
   `−c_1 + c_2(1 − G(ξ(q_1°))) < 0`, and producing exactly `q_1°` is the supplier's unique
   optimal period-1 production. -/
theorem p67_supplier_production (M : Model) (w2 b : ℝ) (q2sel : ℝ → ℝ → ℝ)
    (hq2 : M.IsChainPeriod2Optimal q2sel) :
    (∀ q1 x xx, 0 ≤ q1 → q1 ≤ x → 0 < x → 0 ≤ xx → M.F xx x = M.ratio →
      HasDerivWithinAt (M.supplierProfit1 w2 b q2sel q1) (-M.c1 + M.c2 * (1 - M.G xx))
        (Set.Ici x) x) ∧
    (∀ q1 x xx, 0 ≤ q1 → q1 < x → 0 ≤ xx → M.F xx x = M.ratio →
      HasDerivAt (M.supplierProfit1 w2 b q2sel q1) (-M.c1 + M.c2 * (1 - M.G xx)) x) ∧
    (∀ q1o xi0, 0 < q1o → IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1o →
      0 ≤ xi0 → M.F xi0 q1o = M.ratio →
      -M.c1 + M.c2 * (1 - M.G xi0) < 0 ∧
      ∀ x, 0 ≤ x → x ≠ q1o →
        M.supplierProfit1 w2 b q2sel q1o x < M.supplierProfit1 w2 b q2sel q1o q1o) := by sorry

end CachonCoord.DemandUpdate

