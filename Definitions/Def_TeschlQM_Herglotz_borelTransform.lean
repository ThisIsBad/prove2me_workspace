import Mathlib

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 99, (3.60) (also (3.40)): the **Borel transform** of a Borel measure `μ` on `ℝ`,
`F(z) = ∫_ℝ 1/(λ − z) dμ(λ)`. -/
noncomputable def borelTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ

end TeschlQM.Herglotz
