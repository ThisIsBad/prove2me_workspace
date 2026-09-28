import Mathlib

namespace OnlineConvexOpt.BanditConvex

open MeasureTheory

/-- Eq. (6.4) (Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3,
p. 110, PDF p. 132). The `δ`-smoothed version of `f`, `f̂_δ(x) = E_{v ∈ B}[f(x + δ v)]`, where `v`
is drawn uniformly from the unit ball `B = {v | ‖v‖ ≤ 1}`: the average of `f(x + δ v)` over `v` in
the unit ball, with respect to the ball's normalized volume measure. -/
noncomputable def SmoothedFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal⁻¹ *
    ∫ v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f (x + δ • v)

end OnlineConvexOpt.BanditConvex
