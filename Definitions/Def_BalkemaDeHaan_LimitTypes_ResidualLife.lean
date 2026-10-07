import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.LimitTypes

/-- The distribution tail `R(x) = P{X > x} = μ((x, ∞))` of a law `μ` on `ℝ`
(Balkema, de Haan, *Residual Life Time at Great Age*, Ann. Probab. 2 (1974), p. 792, PDF 1).
For a probability measure `μ` this is `1 - cdf μ x`. -/
noncomputable def tail (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (μ (Set.Ioi x)).toReal

/-- The residual life distribution function of (1), p. 792 (PDF 1):
`F_t(x) = P{X - t ≤ x | X > t} = μ((t, t + x]) / μ((t, ∞))`.
It is `0` for `x < 0` (empty interval). It is meaningful when `μ((t, ∞)) > 0`, which the paper
assumes for every `t` ("`R(x)` is positive for all `x`"); every statement using it carries that
hypothesis. -/
noncomputable def residualCDF (μ : Measure ℝ) (t x : ℝ) : ℝ :=
  (μ (Set.Ioc t (t + x))).toReal / (μ (Set.Ioi t)).toReal

/-- The normed conditional tail of (2), p. 794 (PDF 3):
`P((X - b(t))/a(t) > x | X > t) = μ((t, ∞) ∩ (b(t) + x a(t), ∞)) / μ((t, ∞))`, for `a(t) > 0`.
It equals `min(1, R(b(t) + x a(t)) / R(t))`, the form (3). -/
noncomputable def normedTail (μ : Measure ℝ) (a b : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (μ (Set.Ioi t ∩ Set.Ioi (b t + x * a t))).toReal / (μ (Set.Ioi t)).toReal

/-- Weak convergence, as `t → ∞`, of a family `H t` of distribution functions (or of distribution
tails) to a limit `G`: `H t x → G x` at every continuity point `x` of `G`, and nothing is required
at the discontinuity points of `G`. -/
def WeakConv (H : ℝ → ℝ → ℝ) (G : ℝ → ℝ) : Prop :=
  ∀ x, ContinuousAt G x → Tendsto (fun t => H t x) atTop (𝓝 (G x))

/-- `G` is of type `K`: `G(x) = K(a x + b)` for all `x`, for some `a > 0` and real `b`. -/
def IsOfType (G K : ℝ → ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, ∀ x, G x = K (a * x + b)

end BalkemaDeHaan.LimitTypes
