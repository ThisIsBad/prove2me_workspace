import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Eq. (7.14), p.333 (Marchal's lower bound). For every stationary G/G/1 queue with
`ρ = λ/μ < 1`, the stationary line delay has finite mean and
`W_q ≥ (λ²σ_B² + ρ(ρ − 2)) / (2λ(1 − ρ))`. -/
theorem marchal_lower_bound
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    (lam ^ 2 * serviceVar B + lam / mu * (lam / mu - 2)) / (2 * lam * (1 - lam / mu)) ≤
      meanWait ν := by sorry

end QueueingFundamentals.Bounds

