import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

namespace ShockWear.CumDamage

open MeasureTheory ProbabilityTheory

theorem lemma41 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    ∀ (x : ℝ) (j k : ℕ), 1 ≤ j → j ≤ k →
      cdfPow μ k x ^ (1 / (k : ℝ)) ≤ cdfPow μ j x ^ (1 / (j : ℝ)) := by sorry

end ShockWear.CumDamage

