import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem cor_2_2_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (hammingDistToSet A)) :
    (∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 ≤ t →
      (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
        ≤ ENNReal.ofReal (Real.exp (N * (t ^ 2 / 8) * (1 + 1 / α)))
            / (Measure.pi fun _ : Fin N => μ) A ^ α) ∧
    (0 < (Measure.pi fun _ : Fin N => μ) A → ∀ k : ℝ,
      Real.sqrt (N / 2 * Real.log (1 / ((Measure.pi fun _ : Fin N => μ) A).toReal)) ≤ k →
      (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal k ≤ hammingDistToSet A x}
        ≤ ENNReal.ofReal (Real.exp (-(2 / N) *
            (k - Real.sqrt (N / 2 * Real.log (1 / ((Measure.pi fun _ : Fin N => μ) A).toReal))) ^ 2))) := by sorry

end TalagrandConc.OnePoint

