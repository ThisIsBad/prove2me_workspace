import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley

namespace QueueingFundamentals.GG1

open MeasureTheory

/-- Lindley's equation (6.8) (p.285) for the G/G/1 queue. Let the interarrival times have law `A`
and the service times law `B` (lifetime laws with finite means), and let `ρ = E[S]/E[T] < 1`.
Then (i) a stationary delay distribution exists: a probability law `ν` that Lindley's recursion
`W_q^{(n+1)} = max(0, W_q^{(n)} + S^{(n)} − T^{(n)})` maps to itself; and (ii) the CDF
`W_q = cdfOf ν` of every stationary delay distribution satisfies
`W_q(t) = ∫_{−∞}^{t} W_q(t − x) dU(x) = −∫_0^∞ W_q(y) dU(t − y)` for `0 ≤ t < ∞` and
`W_q(t) = 0` for `t < 0`, where `U` is the law of `S − T` (6.9). The Stieltjes integral
`−∫_0^∞ W_q(y) dU(t − y)` is the integral of `W_q` over `[0, ∞)` against the law of `t − U`. -/
theorem lindley_equation (A B : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B)
    (hAint : Integrable (fun x : ℝ => x) A) (hBint : Integrable (fun x : ℝ => x) B)
    (hmeanA : 0 < meanOf A) (hρ : trafficIntensity A B < 1) :
    (∃ ν : Measure ℝ, IsStationaryDelay A B ν) ∧
    ∀ ν : Measure ℝ, IsStationaryDelay A B ν →
      ∀ t : ℝ,
        (0 ≤ t →
          cdfOf ν t = ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B) ∧
          cdfOf ν t = ∫ y in Set.Ici 0, cdfOf ν y ∂((diffLaw A B).map (fun x => t - x))) ∧
        (t < 0 → cdfOf ν t = 0) := by sorry

end QueueingFundamentals.GG1

