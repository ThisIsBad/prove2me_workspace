import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 8, p. 234: "From (22), `y_r(w₁) > 0` for all `w₁ < w₂`, where recall
`F(0) = 0` is assumed." For `v < w₁ < w₂`, every `y_r` with `F(y_r) = (w₂ - w₁)/(w₂ - v)` is
strictly positive. -/
theorem prebook_positive (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w₁ w₂ : ℝ) (hvw₁ : v < w₁) (hw₁₂ : w₁ < w₂) (hw₂p : w₂ ≤ p)
    (yr : ℝ) (hyr : cdf μ yr = (w₂ - w₁) / (w₂ - v)) :
    0 < yr := by sorry

end CachonPushPull.ShippingCost
