import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem dynamic_marginal_values (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T : ℕ)
    (hlam : IsArrivalModel lam n) (hp : ∀ j, 0 ≤ p j) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T)
    (hx : 1 ≤ x) :
    dynDelta lam p n T t (x + 1) ≤ dynDelta lam p n T t x ∧
      dynDelta lam p n T (t + 1) x ≤ dynDelta lam p n T t x := by sorry

end RevenueManagement
