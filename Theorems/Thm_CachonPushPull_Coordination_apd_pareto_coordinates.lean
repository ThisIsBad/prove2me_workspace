import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game

namespace CachonPushPull.Coordination

open MeasureTheory ProbabilityTheory

/-- Theorem 7, p. 233. Among the push, pull and advance-purchase discount contracts:
1. every contract `{w₁, p}` with `c ≤ w₁ ≤ p` has an outcome and is Pareto;
2. every outcome `(y, q)` of every Pareto contract is efficient: `Π(q) = Π^o = Π(q^o)`;
3. any division of `Π^o` is achievable: for every `r ∈ [0, Π^o]` some contract `{w₁, p}` with
   `c ≤ w₁ ≤ p` has an outcome giving the retailer `r` and the supplier `Π^o - r`. -/
theorem apd_pareto_coordinates (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    (∀ w₁ : ℝ, c ≤ w₁ → w₁ ≤ p →
      (∃ y q : ℝ, IsOutcome μ p c v w₁ p y q) ∧ IsPareto μ p c v w₁ p) ∧
    (∀ w₁ w₂ : ℝ, IsPareto μ p c v w₁ w₂ →
      ∀ y q : ℝ, IsOutcome μ p c v w₁ w₂ y q →
        chainProfit μ p c v q = chainProfit μ p c v qo) ∧
    ∀ r : ℝ, 0 ≤ r → r ≤ chainProfit μ p c v qo →
      ∃ w₁ : ℝ, c ≤ w₁ ∧ w₁ ≤ p ∧ ∃ y q : ℝ, IsOutcome μ p c v w₁ p y q ∧
        retailerProfit μ p v w₁ p y q = r ∧
        supplierProfit μ p c v w₁ p y q = chainProfit μ p c v qo - r := by sorry

end CachonPushPull.Coordination

