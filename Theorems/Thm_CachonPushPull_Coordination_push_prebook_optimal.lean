import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game

namespace CachonPushPull.Coordination

open MeasureTheory ProbabilityTheory

/-- Eq. (3), p. 227: in push mode (the supplier produces exactly the prebook) the retailer's
profit is `π̂_r(q, ŵ₁) = (p - v) S(q) - (ŵ₁ - v) q`. For every prebook price `v < ŵ₁ ≤ p` a
prebook `q ≥ 0` with `F(q) = (p - ŵ₁)/(p - v)` exists, and every such `q` is the unique maximizer
of `π̂_r(·, ŵ₁)` over `[0, ∞)`. -/
theorem push_prebook_optimal (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w : ℝ) (hvw : v < w) (hwp : w ≤ p) :
    (∃ q : ℝ, 0 ≤ q ∧ cdf μ q = (p - w) / (p - v)) ∧
    ∀ q : ℝ, 0 ≤ q → cdf μ q = (p - w) / (p - v) →
      ∀ y : ℝ, 0 ≤ y → y ≠ q →
        (p - v) * S μ y - (w - v) * y < (p - v) * S μ q - (w - v) * q := by sorry

end CachonPushPull.Coordination
