import Mathlib
import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_min_exists (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (Q : ℕ) (hQ : 0 < Q) :
    ∃ Rstar : ℤ, ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ R Q := by sorry

end InventoryControl
