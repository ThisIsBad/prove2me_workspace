import Mathlib

namespace RobustMeanCov.OnePoint

theorem supportGap_monotoneOn (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hconv : ConvexOn ℝ Set.univ (deriv u)) (m : ℝ) :
    MonotoneOn (fun y : ℝ => (u y - u m) / (y - m) ^ 2 - deriv u m / (y - m)) {y : ℝ | y ≠ m} := by sorry

end RobustMeanCov.OnePoint
