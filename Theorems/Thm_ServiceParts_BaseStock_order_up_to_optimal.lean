import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Theorem 2, p. 18, in the n-period form of its proof (lead time τ = 1), corrected at the
base case: (i) for every horizon n ≥ 2 an order-up-to rule is optimal at every inventory
position — either with a real level s, u*(y) = max{0, s − y}, or with level −∞ (never order);
(ii) there is N ≥ 2 such that for every n ≥ N the level can be taken real. -/
theorem order_up_to_optimal (M : Model) :
    (∀ n : ℕ, 2 ≤ n →
        (∃ s : ℝ, M.IsOrderUpToOptimal n s) ∨ (∀ y : ℝ, M.IsOptimalOrder n y 0)) ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∃ s : ℝ, M.IsOrderUpToOptimal n s := by sorry

end ServiceParts.BaseStock

