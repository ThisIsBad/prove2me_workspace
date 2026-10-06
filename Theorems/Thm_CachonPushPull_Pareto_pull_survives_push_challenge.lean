import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Lemma 5, p. 231: all pull contracts with `q ≥ q^P` survive the push challenge. With no
prebook the supplier produces exactly `q`, so the retailer earns the nominal pull profit `π_r(q)`. -/
theorem pull_survives_push_challenge (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qP : ℝ) (hqP : 0 < qP) (hqP_eq : pullRetailerProfit μ p c v qP = pushRetailerProfit μ p v qP) :
    ∀ q : ℝ, qP ≤ q →
      (∀ Q₀ : ℝ, IsSupplierBestReply μ c v (pullPrice μ c v q) (pullPrice μ c v q) 0 Q₀ ↔ Q₀ = q) ∧
      apdRetailerProfit μ p v (pullPrice μ c v q) (pullPrice μ c v q) 0 q =
        pullRetailerProfit μ p c v q ∧
      SurvivesPushChallenge μ p c v q := by sorry

end CachonPushPull.Pareto

