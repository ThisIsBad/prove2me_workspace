import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Contracts

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Theorem 6, p. 231, with Lemma 5: the Pareto set among the admissible push and pull contracts
is exactly the push and pull contracts with `q ∈ [q^P, q^o]`, where `q^P ∈ (0, q^o)` is the unique
positive quantity at which each firm earns the same with the pull and the push contract; and all
those pull contracts survive the push challenge. -/
theorem pareto_set_push_pull (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    ∃ qP : ℝ, 0 < qP ∧ qP < qo ∧
      pullRetailerProfit μ p c v qP = pushRetailerProfit μ p v qP ∧
      pullSupplierProfit μ c v qP = pushSupplierProfit μ p c v qP ∧
      (∀ q : ℝ, 0 < q → pullRetailerProfit μ p c v q = pushRetailerProfit μ p v q → q = qP) ∧
      paretoSet μ p c v = {k : Contract | k.q ∈ Set.Icc qP qo} ∧
      ∀ q ∈ Set.Icc qP qo, SurvivesPushChallenge μ p c v q := by sorry

end CachonPushPull.Pareto

