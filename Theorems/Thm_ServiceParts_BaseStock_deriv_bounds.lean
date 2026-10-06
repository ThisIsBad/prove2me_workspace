import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Section 2.1, p. 20: fₙ is differentiable and "f′ₙ(·) is bounded above and below by
h/(1 − α) and −(c + b), respectively", for every horizon n ≥ 1. -/
theorem deriv_bounds (M : Model) (n : ℕ) (hn : 1 ≤ n) :
    Differentiable ℝ (M.f n) ∧
      ∀ y : ℝ, -(M.c + M.b) ≤ deriv (M.f n) y ∧ deriv (M.f n) y ≤ M.h / (1 - M.α) := by sorry

end ServiceParts.BaseStock

