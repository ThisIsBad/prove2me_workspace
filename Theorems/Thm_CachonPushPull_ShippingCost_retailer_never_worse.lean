import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- §5.1, p. 234: "The retailer is clearly never worse off with an advance-purchase discount
(`w₁ < w₂`) relative to a pull contract (`w₁ = w₂`) for a fixed `w₂`." For a fixed `w₂ < p`
and any `w₁ ≤ w₂`, the retailer's profit in every outcome of `{w₁, w₂}` is at least his profit in
every outcome of the pull contract `{w₂, w₂}`. -/
theorem retailer_never_worse (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₁ w₂ : ℝ) (hw₁₂ : w₁ ≤ w₂) (hw₂p : w₂ < p) :
    ∀ y q y₀ q₀ : ℝ, IsOutcome μ p c v τ w₁ w₂ y q → IsOutcome μ p c v τ w₂ w₂ y₀ q₀ →
      retailerProfit μ p v w₂ w₂ y₀ q₀ ≤ retailerProfit μ p v w₁ w₂ y q := by sorry

end CachonPushPull.ShippingCost

