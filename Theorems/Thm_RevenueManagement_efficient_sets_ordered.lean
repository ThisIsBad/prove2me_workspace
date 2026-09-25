import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem efficient_sets_ordered {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (S S' : Finset (Fin n)) (hS' : IsEfficient P p S')
    (hQ : purchaseProb P S ≤ purchaseProb P S') :
    expRevenue P p S ≤ expRevenue P p S' := by sorry

end RevenueManagement
