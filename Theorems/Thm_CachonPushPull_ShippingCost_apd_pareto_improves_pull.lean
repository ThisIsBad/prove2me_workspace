import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- Theorem 8, p. 234. Let the supplier incur a shipping and handling cost `τ > 0` per at-once
unit (§5.1), and fix the at-once price `w₂ < p`. If the retailer does not prebook under the pull
contract `{w₂, w₂}` (`y = 0` is his unique best reply, `PullNoPrebook`), then there is an
advance-purchase discount `c < w₁ < w₂` such that `{w₁, w₂}` has an outcome, and every outcome
`(y, q)` of `{w₁, w₂}` gives both the retailer and the supplier strictly more profit than the
pull outcome `(0, q₀)`, for every supplier best response `q₀` to the prebook `0` under
`{w₂, w₂}`. -/
theorem apd_pareto_improves_pull (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hw₂p : w₂ < p)
    (hpull : PullNoPrebook μ p c v τ w₂) :
    ∃ w₁ : ℝ, c < w₁ ∧ w₁ < w₂ ∧
      (∃ y q : ℝ, IsOutcome μ p c v τ w₁ w₂ y q) ∧
      ∀ y q : ℝ, IsOutcome μ p c v τ w₁ w₂ y q →
        ∀ q₀ : ℝ, IsSupplierBestResponse μ c v τ w₂ w₂ 0 q₀ →
          retailerProfit μ p v w₂ w₂ 0 q₀ < retailerProfit μ p v w₁ w₂ y q ∧
          supplierProfit μ c v τ w₂ w₂ 0 q₀ < supplierProfit μ c v τ w₁ w₂ y q := by sorry

end CachonPushPull.ShippingCost

