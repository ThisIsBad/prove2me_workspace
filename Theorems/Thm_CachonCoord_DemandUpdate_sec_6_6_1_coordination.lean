import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, pp. 65–67: the buy back contract `{w_1, w_2, b}` with
`λ ∈ [0, 1]`, `p − b = λp`, `w_2 − b = λc_2` and `w_1 − w_2 + λc_2 = λc_1` coordinates the
newsvendor with demand updating:
1. `π_2(q_2|q_1, ξ) = λ(Ω_2(q_2|q_1, ξ) − c_2 q_1) + w_2 q_1`, so the supply chain's period-2
   optimum is the retailer's (and conversely for `λ > 0`);
2. `π_1(q_1) = λΩ_1(q_1)` for `q_1 ≥ 0`, so the supply chain's period-1 optimum is the retailer's
   (and conversely for `λ > 0`);
3. `w_2 − c_2 = w_1 − (λc_1 + (1 − λ)c_2)`, which is `< w_1 − c_1` for `λ < 1` (`=` at `λ = 1`). -/
theorem sec_6_6_1_coordination (M : Model) (lam w1 w2 b : ℝ) (q2sel : ℝ → ℝ → ℝ)
    (hq2 : M.IsChainPeriod2Optimal q2sel) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2)
    (hw1 : w1 - w2 + lam * M.c2 = lam * M.c1) :
    (∀ q1 ξ q2, M.retailerProfit2 w2 b q1 ξ q2 = lam * (M.Omega2 q1 ξ q2 - M.c2 * q1) + w2 * q1) ∧
    (∀ q1 ξ q2, IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2) ∧
    (0 < lam → ∀ q1 ξ q2, IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2) ∧
    (∀ q1, 0 ≤ q1 → M.retailerProfit1 w1 w2 b q2sel q1 = lam * M.Omega1 q2sel q1) ∧
    (∀ q1, 0 ≤ q1 → IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1 →
      IsMaxOn (M.retailerProfit1 w1 w2 b q2sel) (Set.Ici 0) q1) ∧
    (0 < lam → ∀ q1, 0 ≤ q1 → IsMaxOn (M.retailerProfit1 w1 w2 b q2sel) (Set.Ici 0) q1 →
      IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1) ∧
    w2 - M.c2 = w1 - (lam * M.c1 + (1 - lam) * M.c2) ∧
    (lam < 1 → w2 - M.c2 < w1 - M.c1) ∧
    (lam = 1 → w2 - M.c2 = w1 - M.c1) := by sorry

end CachonCoord.DemandUpdate

