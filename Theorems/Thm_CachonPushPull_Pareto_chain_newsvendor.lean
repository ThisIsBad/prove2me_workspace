import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Model

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Eqs. (1)–(2), p. 227: the integrated chain faces a newsvendor problem. -/
theorem chain_newsvendor (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    ConcaveOn ℝ (Set.Ici 0) (chainProfit μ p c v) ∧
    (∃! qo : ℝ, cdf μ qo = (p - c) / (p - v)) ∧
    ∀ qo : ℝ, cdf μ qo = (p - c) / (p - v) →
      0 < qo ∧ IsMaxOn (chainProfit μ p c v) (Set.Ici 0) qo ∧
      StrictMonoOn (chainProfit μ p c v) (Set.Icc 0 qo) := by sorry

end CachonPushPull.Pareto
