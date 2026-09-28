import Mathlib

namespace StochasticOrders.MeanResidualLife

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The mean residual life function `m(t)` of a random variable `X` on `(Ω, μ)` (Shaked &
Shanthikumar, *Stochastic Orders*, Springer 2007, p. 81, Eq. (2.A.1)): `m(t) = E[X - t | X > t]`
for `t < t*`, and `m(t) = 0` otherwise, where `t* = sup{t : P{X>t} > 0}`. The case condition
`t < t*` is formalized directly as `0 < P{X>t}`, its defining equivalent under the monotonicity of
the survival function `t ↦ P{X>t}`, rather than through the derived quantity `t*` itself. -/
noncomputable def mrl (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  if 0 < (μ {ω | t < X ω}).toReal then
    (∫ ω in {ω | t < X ω}, (X ω - t) ∂μ) / (μ {ω | t < X ω}).toReal
  else 0

end StochasticOrders.MeanResidualLife
