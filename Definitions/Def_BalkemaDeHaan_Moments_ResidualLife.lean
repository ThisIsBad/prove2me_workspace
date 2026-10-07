import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife

namespace BalkemaDeHaan.Moments

open MeasureTheory

/-- The conditional distribution function of `X / t` given `X > t` (Theorem 8(a), p. 803):
`P{X/t ≤ x | X > t} = P{t < X ≤ x t} / P{X > t}` for `t > 0`. The quotient is meaningful only when
`P{X > t} > 0`; every statement using it assumes `F(x) < 1` for all `x`. -/
noncomputable def scaledResidualCDF (μ : Measure ℝ) (t x : ℝ) : ℝ :=
  (μ (Set.Ioc t (x * t))).toReal / (μ (Set.Ioi t)).toReal

/-- The conditional moment `E((X/t)^ξ | X > t) = (∫_{(t,∞)} (y/t)^ξ dF(y)) / P{X > t}`
(Theorem 8(a), p. 803), for `t > 0` (so that the base `y / t` of the real power is positive on the
domain of integration). The integral is a Bochner integral: it is meaningful only when the integrand
is integrable, which the statements using it assert or assume explicitly. -/
noncomputable def condMoment (μ : Measure ℝ) (ξ t : ℝ) : ℝ :=
  (∫ y in Set.Ioi t, (y / t) ^ ξ ∂μ) / (μ (Set.Ioi t)).toReal

end BalkemaDeHaan.Moments
