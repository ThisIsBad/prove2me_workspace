import Mathlib
import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

theorem overbooking_limits_decline (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c)
    (hcond : ∀ t, 1 ≤ t → t < M.T →
      0 ≤ M.q t * (M.p t - M.p (t + 1)) + (1 - M.q t) * (M.p t - M.r t))
    (t : ℕ) (ht : 1 ≤ t) (htT : t < M.T) :
    M.overbookingLimit (t + 1) ≤ M.overbookingLimit t := by sorry

end RevenueManagement
