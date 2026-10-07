import Mathlib
import Definitions.Def_TalagrandConc_SKModel_Basic

namespace TalagrandConc.SKModel

/-- Talagrand (12.8), pp. 193 and 195. -/
theorem second_moment :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (ν : MeasureTheory.Measure ℝ)
      [MeasureTheory.IsProbabilityMeasure ν] (β : ℝ),
      8 ≤ N → 0 < β → β < 1 → AdmissibleLaw ν → LightTails ν →
      MeasureTheory.Integrable (partitionFunction N β) (couplingLaw N ν) ∧
      MeasureTheory.Integrable (fun h => partitionFunction N β h ^ 2) (couplingLaw N ν) ∧
      (∫ h, partitionFunction N β h ^ 2 ∂(couplingLaw N ν)) ≤
        K / (1 - β ^ 2) *
          (∫ h, partitionFunction N β h ∂(couplingLaw N ν)) ^ 2 := by sorry

end TalagrandConc.SKModel

