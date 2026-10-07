import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eq. (5.7), p.225: with `ρ = λ E[S] < 1` and a service distribution with finite second
moment and variance `σ_B²`, the stationary departure-point system size has finite mean
`L^{(D)} = ∑ n π_n = ρ + (ρ² + λ² σ_B²) / (2(1 - ρ))`. -/
theorem mean_departure_size (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hint2 : Integrable (fun t : ℝ => t ^ 2) B)
    (hρ : utilization lam B < 1)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π) :
    HasSum (fun n : ℕ => (n : ℝ) * π n)
      (utilization lam B + (utilization lam B ^ 2 + lam ^ 2 * serviceVariance B) /
        (2 * (1 - utilization lam B))) := by sorry

end QueueingFundamentals.MG1

