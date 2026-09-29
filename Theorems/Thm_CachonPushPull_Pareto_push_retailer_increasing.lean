import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Eq. (5), p. 227: the push retailer's profit is increasing in `q`, with
`π̂_r'(q) = (p - v) f(q) q`. -/
theorem push_retailer_increasing (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    (∀ q : ℝ, 0 < q → HasDerivAt (pushRetailerProfit μ p v) ((p - v) * f q * q) q) ∧
    StrictMonoOn (pushRetailerProfit μ p v) (Set.Ici 0) := by sorry

end CachonPushPull.Pareto
