import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model

namespace ShockWear.RandThreshold

open MeasureTheory ProbabilityTheory

theorem proof53_if (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hG : IsNBU (survOf ν)) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    ∀ j k : ℕ, randP μ ν (j + k) ≤ randP μ ν j * randP μ ν k := by sorry

end ShockWear.RandThreshold

