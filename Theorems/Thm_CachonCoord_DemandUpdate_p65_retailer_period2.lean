import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, p. 65 (the display after "With any of those contracts").
With `λ ∈ [0, 1]`, `p − b = λp` and `w_2 − b = λc_2`, the retailer's period-2 profit is
`π_2(q_2|q_1, ξ) = λ(Ω_2(q_2|q_1, ξ) − c_2 q_1) + w_2 q_1`, so every supply chain optimal period-2
order (over `q_2 ≥ q_1`) is optimal for the retailer, and for `λ > 0` conversely: the contract
coordinates the retailer's period-2 decision. -/
theorem p65_retailer_period2 (M : Model) (lam w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2) :
    (∀ q1 ξ q2, M.retailerProfit2 w2 b q1 ξ q2 = lam * (M.Omega2 q1 ξ q2 - M.c2 * q1) + w2 * q1) ∧
    (∀ q1 ξ q2, IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2) ∧
    (0 < lam → ∀ q1 ξ q2, IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2) := by sorry

end CachonCoord.DemandUpdate

