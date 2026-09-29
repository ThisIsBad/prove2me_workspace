import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- §4.2, p. 227 (Lariviere and Porteus 2001): under IGFR the push supplier's profit
`π̂_s(q)` is unimodal in `q`. -/
theorem push_supplier_unimodal (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    ∃ qh : ℝ, 0 < qh ∧
      StrictMonoOn (pushSupplierProfit μ p c v) (Set.Icc 0 qh) ∧
      StrictAntiOn (pushSupplierProfit μ p c v) (Set.Ici qh) := by sorry

end CachonPushPull.Pareto
