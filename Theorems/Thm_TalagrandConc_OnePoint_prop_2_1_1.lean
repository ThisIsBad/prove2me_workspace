import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem prop_2_1_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (hammingDistToSet A)) :
    (∀ t : ℝ, 0 < t →
      (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
          ≤ ENNReal.ofReal (aOne t) ^ N / (Measure.pi fun _ : Fin N => μ) A ∧
      ENNReal.ofReal (aOne t) ^ N / (Measure.pi fun _ : Fin N => μ) A
          ≤ ENNReal.ofReal (Real.exp (t ^ 2 * N / 4)) / (Measure.pi fun _ : Fin N => μ) A) ∧
    (∀ k : ℝ, 0 ≤ k →
      (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal k ≤ hammingDistToSet A x}
          ≤ ENNReal.ofReal (Real.exp (-k ^ 2 / N)) / (Measure.pi fun _ : Fin N => μ) A) := by sorry

end TalagrandConc.OnePoint

