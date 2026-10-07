import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Eq. (7.12), p.332. For a stationary G/G/1 queue with `ρ < 1`, the interdeparture time
`D = S^{(n+1)} + X^{(n)}` (with `S^{(n+1)} ~ B` independent of `(W_q^{(n)}, S^{(n)}, T^{(n)})`)
satisfies `Var[D] = 2σ_B² + σ_A² − 2W_q(1/λ − 1/μ)`. -/
theorem departure_variance
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    variance (fun q : ℝ × (ℝ × ℝ × ℝ) => q.1 + idleX q.2.1 q.2.2.1 q.2.2.2)
        (B.prod (stepLaw ν B A)) =
      2 * serviceVar B + interarrivalVar A - 2 * meanWait ν * (1 / lam - 1 / mu) := by sorry

end QueueingFundamentals.Bounds

