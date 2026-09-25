import Mathlib
import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_joint_optimal (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (hA : 0 < A) (hμ : 0 < μ)
    (CQ : ℕ → ℝ)
    (hCQ : ∀ Q : ℕ, 1 ≤ Q →
      IsLeast (Set.range fun R : ℤ => rqDiscreteCost D h b1 A μ R Q) (CQ Q))
    (Qstar : ℕ) (hQ1 : 1 ≤ Qstar) (hstop : CQ Qstar ≤ CQ (Qstar + 1))
    (hfirst : ∀ Q : ℕ, 1 ≤ Q → Q < Qstar → CQ (Q + 1) < CQ Q)
    (Rstar : ℤ)
    (hR : ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rstar Qstar ≤ rqDiscreteCost D h b1 A μ R Qstar) :
    ∀ (R : ℤ) (Q : ℕ), 1 ≤ Q →
      rqDiscreteCost D h b1 A μ Rstar Qstar ≤ rqDiscreteCost D h b1 A μ R Q := by sorry

end InventoryControl
