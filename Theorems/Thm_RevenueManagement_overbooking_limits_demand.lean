import Mathlib
import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

theorem overbooking_limits_demand (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c)
    (f' : ℕ → ℕ → ℝ) (hf' : ∀ t, (∀ d, 0 ≤ f' t d) ∧ HasSum (f' t) 1)
    (hst : ∀ t k, ∑' d, (if k ≤ d then M.f t d else 0) ≤ ∑' d, (if k ≤ d then f' t d else 0))
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ M.T) :
    ({ M with f := f' } : DynOverbooking).overbookingLimit t ≤ M.overbookingLimit t := by sorry

end RevenueManagement
