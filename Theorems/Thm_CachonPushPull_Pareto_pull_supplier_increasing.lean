import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Eq. (9), p. 227: the pull supplier's profit is increasing in `q`, with
`π_s'(q) = (p - v)(1 - F(q^o)) j(q) h(q)`. -/
theorem pull_supplier_increasing (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    (∀ q : ℝ, 0 < q → HasDerivAt (pullSupplierProfit μ c v)
      ((p - v) * (1 - cdf μ qo) * j μ q * hazard μ f q) q) ∧
    StrictMonoOn (pullSupplierProfit μ c v) (Set.Ici 0) := by sorry

end CachonPushPull.Pareto
