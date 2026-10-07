import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Eq. (7.13), p.333 (Kingman's upper bound). For every stationary G/G/1 queue with
`ρ = λ/μ < 1`, the stationary line delay has finite mean and
`W_q ≤ λ(σ_A² + σ_B²) / (2(1 − ρ))`. -/
theorem kingman_upper_bound
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    meanWait ν ≤ lam * (interarrivalVar A + serviceVar B) / (2 * (1 - lam / mu)) := by sorry

end QueueingFundamentals.Bounds

