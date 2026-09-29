import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- Eq. (22), p. 233: under a contract with `v < w₁ ≤ w₂ ≤ p` and any fixed production `q`, the
retailer's profit `π_r(y, q)` is concave in the prebook `y ≥ 0`, a prebook `y_r ≥ 0` with
`F(y_r) = (w₂ - w₁)/(w₂ - v)` exists, and every such `y_r` is the unique maximizer of
`y ↦ π_r(y, q)` over `y ≥ 0`; in particular `y_r` does not depend on `q`. -/
theorem retailer_prebook_argmax (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w₁ w₂ : ℝ) (hvw₁ : v < w₁) (hw₁₂ : w₁ ≤ w₂) (hw₂p : w₂ ≤ p) (q : ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q) ∧
    (∃ yr : ℝ, 0 ≤ yr ∧ cdf μ yr = (w₂ - w₁) / (w₂ - v)) ∧
    ∀ yr : ℝ, 0 ≤ yr → cdf μ yr = (w₂ - w₁) / (w₂ - v) →
      ∀ y : ℝ, 0 ≤ y → y ≠ yr →
        retailerProfit μ p v w₁ w₂ y q < retailerProfit μ p v w₁ w₂ yr q := by sorry

end CachonPushPull.ShippingCost
