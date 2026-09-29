import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

/-- Lemma 2 (Zheng 1992, p. 90): for any `Q > 0`, an optimal reorder point `r(Q)` exists (the
chosen one, `optReorder`, minimizes `c(Q, ·)`), and `r` minimizes `c(Q, ·)` iff
`G(r) = G(r + Q)`. -/
theorem reorder_opt_iff
    {lam L K h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hK : 0 < K) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y)
    {Q : ℝ} (hQ : 0 < Q) :
    IsOptReorder (newsvendorCost h p μ) lam K Q (optReorder (newsvendorCost h p μ) Q) ∧
    ∀ r : ℝ, IsOptReorder (newsvendorCost h p μ) lam K Q r ↔
      newsvendorCost h p μ r = newsvendorCost h p μ (r + Q) := by sorry

end ZhengQR.OrderQty
