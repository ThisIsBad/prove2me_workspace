import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem littlewood_marginal_value (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hf : ∀ j, IsPmf (f j))
    (hp : ∀ j, 0 ≤ p j) (x : ℕ) (hx : 1 ≤ x) :
    staticDelta p f 1 x = p 1 * ∑' d, (if x ≤ d then f 1 d else 0) ∧
      (IsStageOptimal p f 1 x 1 1 ↔ p 1 * ∑' d, (if x ≤ d then f 1 d else 0) ≤ p 2) := by sorry

end RevenueManagement
