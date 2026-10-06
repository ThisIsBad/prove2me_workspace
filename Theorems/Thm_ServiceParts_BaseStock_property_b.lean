import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Property (b) in the proof of Theorem 2, p. 19 (re-established as (2.10), p. 20): if the
order-up-to rule with level s is optimal in the n-period problem (n ≥ 2), then fₙ is
differentiable at every y, with f′ₙ(y) = −c + L′(y) for y < s and
f′ₙ(y) = L′(y) + α ∫₀^∞ f′ₙ₋₁(y − x) g(x) dx for y ≥ s. -/
theorem property_b (M : Model) (n : ℕ) (hn : 2 ≤ n) (s : ℝ)
    (hs : M.IsOrderUpToOptimal n s) (y : ℝ) :
    HasDerivAt (M.f n)
      (if y < s then -M.c + deriv M.L y
       else deriv M.L y + M.α * ∫ x in Ioi (0 : ℝ), deriv (M.f (n - 1)) (y - x) * M.g x) y := by sorry

end ServiceParts.BaseStock

