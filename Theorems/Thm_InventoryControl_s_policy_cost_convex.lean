import Mathlib
import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem s_policy_cost_convex (D : DiscreteDemand) (h b1 : ℝ) (hh : 0 < h) (hb : 0 < b1) :
    (∀ k : ℤ, sPolicyCost D h b1 (k + 1) - sPolicyCost D h b1 k
        ≤ sPolicyCost D h b1 (k + 2) - sPolicyCost D h b1 (k + 1))
      ∧ Filter.Tendsto (sPolicyCost D h b1) (Filter.cocompact ℤ) Filter.atTop := by sorry

end InventoryControl
