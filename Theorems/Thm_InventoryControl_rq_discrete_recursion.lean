import Mathlib
import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_recursion (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (Q : ℕ) (hQ : 0 < Q) (Rstar : ℤ)
    (hR : ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ R Q) :
    let Rnext : ℤ := if sPolicyCost D h b1 Rstar ≤ sPolicyCost D h b1 (Rstar + Q + 1)
      then Rstar - 1 else Rstar
    (∀ R : ℤ, rqDiscreteCost D h b1 A μ Rnext (Q + 1) ≤ rqDiscreteCost D h b1 A μ R (Q + 1))
      ∧ rqDiscreteCost D h b1 A μ Rnext (Q + 1)
          = rqDiscreteCost D h b1 A μ Rstar Q * (Q / (Q + 1 : ℝ))
            + min (sPolicyCost D h b1 Rstar) (sPolicyCost D h b1 (Rstar + Q + 1))
                * (1 / (Q + 1 : ℝ)) := by sorry

end InventoryControl
