import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

/-- Eq. (7) (Zheng 1992, p. 91): for `Q > 0`, `∫_{r(Q)}^{r(Q)+Q} G = ∫_0^Q H`, and hence
`C(Q) = (λK + ∫_0^Q H(y) dy) / Q`. -/
theorem integral_H_eq
    {lam L K h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hK : 0 < K) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y)
    {Q : ℝ} (hQ : 0 < Q) :
    (∫ y in optReorder (newsvendorCost h p μ) Q..optReorder (newsvendorCost h p μ) Q + Q,
        newsvendorCost h p μ y) =
      (∫ y in (0 : ℝ)..Q, Hfun (newsvendorCost h p μ) y) ∧
    optCost (newsvendorCost h p μ) lam K Q =
      (lam * K + ∫ y in (0 : ℝ)..Q, Hfun (newsvendorCost h p μ) y) / Q := by sorry

end ZhengQR.OrderQty
