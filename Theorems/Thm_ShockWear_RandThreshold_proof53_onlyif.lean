import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model

namespace ShockWear.RandThreshold

open MeasureTheory ProbabilityTheory

theorem proof53_onlyif (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hsub : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
      ∀ j k : ℕ, randP μ ν (j + k) ≤ randP μ ν j * randP μ ν k) :
    ∀ s : ℝ, 0 < s → ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ,
      survOf ν (s + j * (s / k)) ≤ survOf ν s * survOf ν (j * (s / k)) := by sorry

end ShockWear.RandThreshold

