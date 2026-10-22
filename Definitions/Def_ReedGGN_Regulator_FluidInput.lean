import Mathlib

namespace ReedGGN.Regulator

open MeasureTheory

/-- The tail `G(t) = 1 − F(t) = μ((t, ∞))` of the law `μ` of a service time (p. 6). -/
noncomputable def tail (μ : Measure ℝ) (t : ℝ) : ℝ :=
  (μ (Set.Ioi t)).toReal

/-- The equilibrium distribution (5.4) (p. 18): `F_e(x) = ∫_0^x G(u) du` (Lebesgue measure),
for `x ≥ 0`; for `x < 0` the integral is over the empty set and the value is `0`. -/
noncomputable def Fe (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ u in Set.Icc 0 x, tail μ u

/-- The first three terms of the fluid equation (4.7) (p. 12) when the fluid arrival process is
`Ā = e`, the identity `e(t) = t` (so `dĀ(s) = ds`):
`min(Q̄₀, 1) F̄₀(t) + (Q̄₀ − 1)^+ G(t) + ∫_0^t G(t − s) ds`.
Here `Q0` is `Q̄₀`, `F0bar` is the tail `F̄₀ = 1 − F₀` of the initial residual service law, and
`G` is the tail of the service law `μ`. -/
noncomputable def fluidInput (Q0 : ℝ) (F0bar : ℝ → ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  min Q0 1 * F0bar t + max (Q0 - 1) 0 * tail μ t + ∫ s in Set.Icc 0 t, tail μ (t - s)

end ReedGGN.Regulator
