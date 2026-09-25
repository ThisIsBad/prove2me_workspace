import Mathlib
import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_marginal_mono (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (Q : ℕ) (hQ : 0 < Q) (Rstar Rnext : ℤ)
    (hR : ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ R Q)
    (hR' : ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rnext (Q + 1) ≤ rqDiscreteCost D h b1 A μ R (Q + 1)) :
    (rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ Rnext (Q + 1)
        ↔ rqDiscreteCost D h b1 A μ Rstar Q
            ≤ min (sPolicyCost D h b1 Rstar) (sPolicyCost D h b1 (Rstar + Q + 1)))
      ∧ min (sPolicyCost D h b1 Rstar) (sPolicyCost D h b1 (Rstar + Q + 1))
          ≤ min (sPolicyCost D h b1 Rnext) (sPolicyCost D h b1 (Rnext + (Q + 1) + 1)) := by sorry

end InventoryControl
