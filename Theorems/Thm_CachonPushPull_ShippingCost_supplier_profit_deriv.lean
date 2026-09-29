import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- The derivative display in the proof of Theorem 8, p. 234. Fix `w₂ ≤ p`, a production `q` and
the retailer's prebook `y_r(w₁) ≥ 0`, `F(y_r(w₁)) = (w₂ - w₁)/(w₂ - v)` (Eq. (22)), for
`v < w₁ < w₂`. At a point `w₁` of that interval where the density at `y_r(w₁)` is positive
(the hypothesis of the implicit function step), `y_r` is differentiable with
`y_r'(w₁) = -[(w₂ - v) f(y_r(w₁))]⁻¹`, and
`d π_s(y_r(w₁), q)/d w₁ = y_r(w₁) - [(w₁ - v) - (w₂ - τ - v)(1 - F(y_r(w₁)))]/((w₂ - v) f(y_r(w₁)))`. -/
theorem supplier_profit_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hw₂p : w₂ ≤ p) (yr : ℝ → ℝ)
    (hyr : ∀ w : ℝ, w ∈ Set.Ioo v w₂ → 0 ≤ yr w ∧ cdf μ (yr w) = (w₂ - w) / (w₂ - v))
    (q w₁ : ℝ) (hw₁ : w₁ ∈ Set.Ioo v w₂) (hf : 0 < f (yr w₁)) :
    HasDerivAt yr (-((w₂ - v) * f (yr w₁))⁻¹) w₁ ∧
    HasDerivAt (fun w : ℝ => supplierProfit μ c v τ w w₂ (yr w) q)
      (yr w₁ - ((w₁ - v) - (w₂ - τ - v) * (1 - cdf μ (yr w₁))) / ((w₂ - v) * f (yr w₁)))
      w₁ := by sorry

end CachonPushPull.ShippingCost
