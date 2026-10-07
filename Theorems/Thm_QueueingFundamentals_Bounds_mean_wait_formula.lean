import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Eq. (7.7), p.331. For a stationary G/G/1 queue with `ρ < 1`, the stationary line delay has
finite mean `W_q = E[W_q^{(n)}]` and `W_q = (E[X²] − E[U²]) / (2E[U])`. -/
theorem mean_wait_formula
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    meanWait ν =
      (∫ p, idleX p.1 p.2.1 p.2.2 ^ 2 ∂(stepLaw ν B A) - ∫ p, (p.2.1 - p.2.2) ^ 2 ∂(stepLaw ν B A)) /
        (2 * ∫ p, (p.2.1 - p.2.2) ∂(stepLaw ν B A)) := by sorry

end QueueingFundamentals.Bounds

