import Mathlib
import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

theorem overbooking_limit_policy (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c)
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ M.T) (y d : ℕ) :
    M.IsOptimalLevel t y d (limitPolicy (M.overbookingLimit t) y d) := by sorry

end RevenueManagement
