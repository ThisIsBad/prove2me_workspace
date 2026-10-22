import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model

namespace ShockWear.RandThreshold

open MeasureTheory ProbabilityTheory

theorem theorem53 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0) :
    ((∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
        ∀ j k : ℕ, randP μ ν (j + k) ≤ randP μ ν j * randP μ ν k) ↔ IsNBU (survOf ν)) ∧
    (IsNBU (survOf ν) → ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
        ∀ lam : ℝ, 0 < lam → IsNBU (shockSurv lam (randP μ ν))) := by sorry

end ShockWear.RandThreshold

