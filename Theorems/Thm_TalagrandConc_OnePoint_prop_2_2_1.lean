import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem prop_2_2_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (hammingDistToSet A)) (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
      ≤ ENNReal.ofReal (aAlpha α t) ^ N / (Measure.pi fun _ : Fin N => μ) A ^ α := by sorry

end TalagrandConc.OnePoint

