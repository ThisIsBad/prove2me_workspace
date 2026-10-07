import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain
import Definitions.Def_QueueingFundamentals_MG1_transforms

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eq. (5.34), p.237. Under the hypotheses of (5.33), let `W_q` be a probability distribution on
`[0, ∞)` (the FCFS line-wait distribution) with `W = W_q * B`, the convolution expressing
`T = T_q + S` with `T_q` and `S` independent. Then for every real `s > 0`,
`W_q*(s) = (1 - ρ) s / (s - λ[1 - B*(s)])`. -/
theorem queue_wait_lst (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hρ : utilization lam B < 1)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π)
    (W : Measure ℝ) [IsProbabilityMeasure W] (hW : W (Set.Iio 0) = 0)
    (hπW : ∀ n : ℕ, π n = ∫ t, (lam * t) ^ n * Real.exp (-(lam * t)) / (Nat.factorial n : ℝ) ∂W)
    (Wq : Measure ℝ) [IsProbabilityMeasure Wq] (hWq : Wq (Set.Iio 0) = 0)
    (hconv : W = Wq.conv B) :
    ∀ s : ℝ, 0 < s →
      lst Wq s = (1 - (utilization lam B : ℂ)) * s / (s - lam * (1 - lst B s)) := by sorry

end QueueingFundamentals.MG1

