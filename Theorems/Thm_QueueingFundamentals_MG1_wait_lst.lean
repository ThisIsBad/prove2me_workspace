import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain
import Definitions.Def_QueueingFundamentals_MG1_transforms

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eqs. (5.29) and (5.33), pp.235–237. Let `ρ = λ E[S] < 1`, let `π` be the stationary
departure-point distribution, and let `W` be a probability distribution on `[0, ∞)` (the FCFS
system-wait distribution) with `π_n = (1/n!) ∫_0^∞ (λt)^n e^{-λt} dW(t)` for all `n` (p.235).
Then `Π(z) = W*[λ(1 - z)]` for `|z| ≤ 1` (5.29), and for every real `s > 0`,
`W*(s) = (1 - ρ) s B*(s) / (s - λ[1 - B*(s)])` (5.33). -/
theorem wait_lst (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hρ : utilization lam B < 1)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π)
    (W : Measure ℝ) [IsProbabilityMeasure W] (hW : W (Set.Iio 0) = 0)
    (hπW : ∀ n : ℕ, π n = ∫ t, (lam * t) ^ n * Real.exp (-(lam * t)) / (Nat.factorial n : ℝ) ∂W) :
    (∀ z : ℂ, ‖z‖ ≤ 1 → pgf π z = lst W ((lam : ℂ) * (1 - z))) ∧
    ∀ s : ℝ, 0 < s →
      lst W s = (1 - (utilization lam B : ℂ)) * s * lst B s / (s - lam * (1 - lst B s)) := by sorry

end QueueingFundamentals.MG1

