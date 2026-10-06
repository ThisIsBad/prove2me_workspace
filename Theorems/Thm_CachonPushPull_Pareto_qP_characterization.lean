import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Lemma 4, p. 230: the quantity `q^P` exists; it is the unique positive quantity where the
retailer is indifferent between pull and push, the unique positive quantity where the supplier is
indifferent, the unique maximizer of `π_r(q) - π̂_s(q)`, and it exceeds every maximizer `q*` of
`π_r`. -/
theorem qP_characterization (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    ∃ qP : ℝ, 0 < qP ∧
      (∀ q : ℝ, 0 < q → (pullRetailerProfit μ p c v q = pushRetailerProfit μ p v q ↔ q = qP)) ∧
      (∀ q : ℝ, 0 < q → (pullSupplierProfit μ c v q = pushSupplierProfit μ p c v q ↔ q = qP)) ∧
      IsMaxOn (fun q : ℝ => pullRetailerProfit μ p c v q - pushSupplierProfit μ p c v q)
        (Set.Ici 0) qP ∧
      (∀ q : ℝ, 0 ≤ q →
        IsMaxOn (fun q : ℝ => pullRetailerProfit μ p c v q - pushSupplierProfit μ p c v q)
          (Set.Ici 0) q → q = qP) ∧
      (∀ qstar : ℝ, 0 ≤ qstar → IsMaxOn (pullRetailerProfit μ p c v) (Set.Ici 0) qstar →
        qstar < qP) := by sorry

end CachonPushPull.Pareto

