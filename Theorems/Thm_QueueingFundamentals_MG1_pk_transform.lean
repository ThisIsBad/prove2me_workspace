import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eqs. (5.15)–(5.16), p.227, the Pollaczek–Khintchine transform formula. Let `λ > 0`, let the
service distribution `B` be a probability measure on `[0, ∞)` with finite mean `E[S]`, and
let `ρ = λ E[S] < 1`. Then the M/G/1 departure-point chain (5.10) has a stationary probability
vector, and every stationary probability vector `π` has `π_0 = 1 - ρ` and, for every
`|z| ≤ 1` with `z ≠ 1`, `K(z) ≠ z` and
`Π(z) = (1 - ρ)(1 - z) K(z) / (K(z) - z)`. At `z = 1` the right side is `0/0`; there
`Π(1) = 1`, which is part of `IsStationaryDist`. -/
theorem pk_transform (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hρ : utilization lam B < 1) :
    (∃ π : ℕ → ℝ, IsStationaryDist (transitionMatrix lam B) π) ∧
      ∀ π : ℕ → ℝ, IsStationaryDist (transitionMatrix lam B) π →
        π 0 = 1 - utilization lam B ∧
        ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 →
          pgf (arrivalProb lam B) z ≠ z ∧
          pgf π z = (1 - (utilization lam B : ℂ)) * (1 - z) * pgf (arrivalProb lam B) z /
            (pgf (arrivalProb lam B) z - z) := by sorry

end QueueingFundamentals.MG1

