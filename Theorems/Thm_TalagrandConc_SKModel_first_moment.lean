import Mathlib
import Definitions.Def_TalagrandConc_SKModel_Basic

namespace TalagrandConc.SKModel

/-- Talagrand (12.7), p. 193. -/
theorem first_moment :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (ν : MeasureTheory.Measure ℝ)
      [MeasureTheory.IsProbabilityMeasure ν] (β : ℝ),
      1 ≤ N → 0 < β → β ≤ 1 → AdmissibleLaw ν → LightTails ν →
      MeasureTheory.Integrable (partitionFunction N β) (couplingLaw N ν) ∧
      K⁻¹ * Real.exp (β ^ 2 * N / 4) ≤
        ∫ h, partitionFunction N β h ∂(couplingLaw N ν) ∧
      (∫ h, partitionFunction N β h ∂(couplingLaw N ν)) ≤
        K * Real.exp (β ^ 2 * N / 4) := by sorry

end TalagrandConc.SKModel

