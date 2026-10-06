import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

open Filter Topology

/-- The limit display in the proof of Theorem 8, p. 234. Fix `v < w₂ ≤ p`, `τ > 0`, a production
`q` and the retailer's prebook `y_r(w₁) ≥ 0`, `F(y_r(w₁)) = (w₂ - w₁)/(w₂ - v)`, for
`v < w₁ < w₂`. Then `y_r(w₁) → 0` as `w₁ → w₂⁻`. If moreover the density has a positive right
limit `f(0) := lim_{x → 0⁺} f(x) > 0` (the display's hypothesis), then
`lim_{w₁ → w₂⁻} d π_s(y_r(w₁), q)/d w₁ = -τ/((w₂ - v) f(0)) < 0`. -/
theorem supplier_profit_deriv_limit (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hvw₂ : v < w₂) (hw₂p : w₂ ≤ p) (yr : ℝ → ℝ)
    (hyr : ∀ w : ℝ, w ∈ Set.Ioo v w₂ → 0 ≤ yr w ∧ cdf μ (yr w) = (w₂ - w) / (w₂ - v))
    (q : ℝ) :
    Tendsto yr (𝓝[<] w₂) (𝓝 0) ∧
    ∀ f₀ : ℝ, 0 < f₀ → Tendsto f (𝓝[>] 0) (𝓝 f₀) →
      Tendsto (fun w₁ : ℝ => deriv (fun w : ℝ => supplierProfit μ c v τ w w₂ (yr w) q) w₁)
          (𝓝[<] w₂) (𝓝 (-τ / ((w₂ - v) * f₀))) ∧
        -τ / ((w₂ - v) * f₀) < 0 := by sorry

end CachonPushPull.ShippingCost

