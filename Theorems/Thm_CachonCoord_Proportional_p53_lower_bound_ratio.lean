import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 53: the coordinating contract with `b = 0` gives the supplier the share `(n − 1)/n` of the
optimal supply chain profit, `π_s(q°, w_b(0), 0)/Π(q°) = (n − 1)/n` (and `Π(q°) > 0`). -/
theorem p53_lower_bound_ratio (M : Model) (n : ℕ) (hn : 2 ≤ n) (qo : ℝ)
    (hqo : M.F qo = (M.p - M.c) / M.p) :
    0 < M.chainProfit qo ∧
      M.supplierProfit (M.wb n 0 qo) 0 qo / M.chainProfit qo = ((n : ℝ) - 1) / n := by sorry

end CachonCoord.Proportional

