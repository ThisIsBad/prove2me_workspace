import Mathlib
import Definitions.Def_RevenueManagement_dynamicPricing

namespace RevenueManagement

theorem bernoulli_marginal_values (p : ℕ → ℝ → ℝ) (T : ℕ)
    (hr : ∀ t, ConcaveOn ℝ (Set.Icc 0 1) (revenueRate p t)) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T)
    (hx : 1 ≤ x) :
    bernoulliDelta p T (t + 1) x ≤ bernoulliDelta p T t x ∧
      bernoulliDelta p T t (x + 1) ≤ bernoulliDelta p T t x := by sorry

end RevenueManagement
