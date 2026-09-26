import Definitions.Def_RevenueManagement_dynamicPricing

namespace RevenueManagement

theorem deterministic_upper_bound (p : ℕ → ℝ → ℝ) (T : ℕ)
    (hr : ∀ t, ConcaveOn ℝ (Set.Icc 0 1) (revenueRate p t)) (C : ℕ) :
    bernoulliValue p T 1 C ≤ deterministicValue p T 1 C := by sorry

end RevenueManagement
