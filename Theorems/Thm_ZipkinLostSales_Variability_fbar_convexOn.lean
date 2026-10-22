import Mathlib
import Definitions.Def_ZipkinLostSales_Variability_Model
open MeasureTheory

namespace ZipkinLostSales.Variability

/-- Theorem 4 (Zipkin 2008, p. 939) with the remark of §3 (p. 938) that L♮-convexity implies
ordinary convexity, for the model's value functions: for one demand law `μ` and every number of
periods to go `k`, `f̄` is convex on the state space `V`. -/
theorem fbar_convexOn {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) :
    ∀ k : ℕ, ConvexOn ℝ (ZipkinLostSales.LNatural.V L) (ZipkinLostSales.LNatural.fbar c hh p γ μ k) := by sorry

end ZipkinLostSales.Variability

