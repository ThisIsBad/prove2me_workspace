import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem static_marginal_values (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hf : ∀ j, IsPmf (f j))
    (hp : ∀ j, 0 ≤ p j) (j x : ℕ) (hx : 1 ≤ x) :
    staticDelta p f j (x + 1) ≤ staticDelta p f j x ∧
      staticDelta p f j x ≤ staticDelta p f (j + 1) x := by sorry

end RevenueManagement
