import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Theorem 2, p. 228: the retailer's profit with a pull contract, `π_r(q)`, is concave
in `q` (strictly, as the proof establishes). -/
theorem pull_retailer_concave (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    StrictConcaveOn ℝ (Set.Ici 0) (pullRetailerProfit μ p c v) := by sorry

end CachonPushPull.Pareto
