import Mathlib
import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_cost_diff (D : DiscreteDemand) (h b1 A μ : ℝ) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) :
    rqDiscreteCost D h b1 A μ (R + 1) Q - rqDiscreteCost D h b1 A μ R Q
      = -b1 + (h + b1) * rqDiscreteReadyRate D (R + 1) Q := by sorry

end InventoryControl
