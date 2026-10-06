import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Theorem 3, p. 229: the retailer's maximum profit with pull exceeds the supplier's maximum
profit with push, `q* > q̂*`, and `Π(q*) > Π(q̂*)`. -/
theorem pull_beats_push_maxima (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    (∃ qstar : ℝ, 0 ≤ qstar ∧ IsMaxOn (pullRetailerProfit μ p c v) (Set.Ici 0) qstar) ∧
    (∃ qhat : ℝ, 0 ≤ qhat ∧ IsMaxOn (pushSupplierProfit μ p c v) (Set.Ici 0) qhat) ∧
    ∀ qstar qhat : ℝ, 0 ≤ qstar → IsMaxOn (pullRetailerProfit μ p c v) (Set.Ici 0) qstar →
      0 ≤ qhat → IsMaxOn (pushSupplierProfit μ p c v) (Set.Ici 0) qhat →
      pushSupplierProfit μ p c v qhat < pullRetailerProfit μ p c v qstar ∧
      qhat < qstar ∧
      chainProfit μ p c v qhat < chainProfit μ p c v qstar := by sorry

end CachonPushPull.Pareto

