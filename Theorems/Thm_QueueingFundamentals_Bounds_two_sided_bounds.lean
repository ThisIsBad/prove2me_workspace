import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Eq. (7.17), p.336. For a stationary G/G/1 queue with `ρ < 1`, with `r₀` the unique
nonnegative root of `f(z) = z − ∫_{−z}^{∞} [1 − U(t)] dt`:
`max(0, r₀, (λ²σ_B² + ρ(ρ − 2))/(2λ(1 − ρ))) ≤ W_q ≤ λ(σ_A² + σ_B²)/(2(1 − ρ))`. -/
theorem two_sided_bounds
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    (∃! r : ℝ, 0 ≤ r ∧ rootFun A B r = 0) ∧
    Integrable (fun w : ℝ => w) ν ∧
    ∀ r : ℝ, 0 ≤ r → rootFun A B r = 0 →
      max (max 0 r)
          ((lam ^ 2 * serviceVar B + lam / mu * (lam / mu - 2)) / (2 * lam * (1 - lam / mu))) ≤
        meanWait ν ∧
      meanWait ν ≤ lam * (interarrivalVar A + serviceVar B) / (2 * (1 - lam / mu)) := by sorry

end QueueingFundamentals.Bounds

