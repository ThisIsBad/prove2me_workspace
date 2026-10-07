import Mathlib

open MeasureTheory

namespace BalkemaDeHaan.ParetoBounds

/-- The residual life distribution function (1) of Balkema–de Haan (1974), p. 792:
for a lifetime `X` with law `μ`, `F_t(x) = P{X - t ≤ x | X > t}
= μ((t, t + x]) / μ((t, ∞))`. It is `0` for `x < 0` (empty interval). -/
noncomputable def residualLife (μ : Measure ℝ) (t x : ℝ) : ℝ :=
  (μ (Set.Ioc t (t + x))).toReal / (μ (Set.Ioi t)).toReal

end BalkemaDeHaan.ParetoBounds
