import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem remark_2_1_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (weightedHammingDistToSet a A)) :
    (∀ t : ℝ, 0 < t →
      (∫⁻ x, expMul t (weightedHammingDistToSet a A x) ∂(Measure.pi fun _ : Fin N => μ))
          ≤ ENNReal.ofReal (Real.exp (t ^ 2 * (∑ i, a i ^ 2) / 4))
              / (Measure.pi fun _ : Fin N => μ) A) ∧
    (∀ u : ℝ, 0 ≤ u →
      (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal u ≤ weightedHammingDistToSet a A x}
          ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / ∑ i, a i ^ 2))
              / (Measure.pi fun _ : Fin N => μ) A) := by sorry

end TalagrandConc.OnePoint

