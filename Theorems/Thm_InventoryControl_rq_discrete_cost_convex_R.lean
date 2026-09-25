import Mathlib
import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_cost_convex_R (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (Q : ℕ) (hQ : 0 < Q) (R : ℤ) :
    rqDiscreteCost D h b1 A μ (R + 1) Q - rqDiscreteCost D h b1 A μ R Q
      ≤ rqDiscreteCost D h b1 A μ (R + 2) Q - rqDiscreteCost D h b1 A μ (R + 1) Q := by sorry

end InventoryControl
