import Mathlib
import Definitions.Def_TeschlQM_Herglotz_IsHerglotz
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Definitions.Def_TeschlQM_Herglotz_measureSpectrum

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 99, Theorem 3.10. The Borel transform `F` of a finite Borel measure `μ` on `ℝ` is
a Herglotz function (for `μ ≠ 0`: the transform of the zero measure is `F ≡ 0`, which does not
map `ℂ₊` into the open upper half plane), it is holomorphic on `ℂ \ σ(μ)`, and (3.61)
`F(z*) = F(z)*` and `|F(z)| ≤ μ(ℝ)/Im(z)` for `z ∈ ℂ₊`. -/
theorem borelTransform_isHerglotz (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (μ ≠ 0 → IsHerglotz (borelTransform μ)) ∧
    DifferentiableOn ℂ (borelTransform μ) {z : ℂ | ∀ t ∈ measureSpectrum μ, z ≠ (t : ℂ)} ∧
    ∀ z : ℂ, 0 < z.im →
      borelTransform μ (starRingEnd ℂ z) = starRingEnd ℂ (borelTransform μ z) ∧
      ‖borelTransform μ z‖ ≤ (μ Set.univ).toReal / z.im := by sorry

end TeschlQM.Herglotz
