import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, p. 66 (the displays for `π_1`, `Ω_1` and `π_1 = λΩ_1`).
Let `q2sel` select a supply chain optimal period-2 order `q_2(q_1, ξ)`. With a coordinating
`{w_2, b}` pair (`λ ∈ [0, 1]`, `p − b = λp`, `w_2 − b = λc_2`), for every `q_1 ≥ 0`
1. `π_1(q_1) = −(w_1 − w_2 + λc_2)q_1 + λE[Ω_2(q_2(q_1, ξ)|q_1, ξ)]`;
2. if moreover `w_1 − w_2 + λc_2 = λc_1`, then `π_1(q_1) = λΩ_1(q_1)`;
and then every supply chain optimal `q_1 ≥ 0` is optimal for the retailer, and for `λ > 0`
conversely. -/
theorem p66_retailer_period1 (M : Model) (lam w1 w2 b : ℝ) (q2sel : ℝ → ℝ → ℝ)
    (hq2 : M.IsChainPeriod2Optimal q2sel) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2) :
    (∀ q1, 0 ≤ q1 → M.retailerProfit1 w1 w2 b q2sel q1 =
      -(w1 - w2 + lam * M.c2) * q1 + lam * M.E (fun ξ => M.Omega2 q1 ξ (q2sel q1 ξ))) ∧
    (w1 - w2 + lam * M.c2 = lam * M.c1 →
      (∀ q1, 0 ≤ q1 → M.retailerProfit1 w1 w2 b q2sel q1 = lam * M.Omega1 q2sel q1) ∧
      (∀ q1, 0 ≤ q1 → IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1 →
        IsMaxOn (M.retailerProfit1 w1 w2 b q2sel) (Set.Ici 0) q1) ∧
      (0 < lam → ∀ q1, 0 ≤ q1 → IsMaxOn (M.retailerProfit1 w1 w2 b q2sel) (Set.Ici 0) q1 →
        IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1)) := by sorry

end CachonCoord.DemandUpdate

