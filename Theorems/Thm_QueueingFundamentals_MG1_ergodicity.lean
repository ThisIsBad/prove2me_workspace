import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- §5.1.4, pp.233–235: for Poisson(`λ`) arrivals and a service distribution `B` on `[0, ∞)`
with finite mean `E[S]`, the M/G/1 departure-point chain (5.10) has a stationary distribution,
and then exactly one, if and only if `ρ = λ E[S] < 1`. -/
theorem ergodicity (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) :
    (∃! π : ℕ → ℝ, IsStationaryDist (transitionMatrix lam B) π) ↔ utilization lam B < 1 := by sorry

end QueueingFundamentals.MG1

