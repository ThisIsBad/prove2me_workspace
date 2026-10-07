import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_ResidualLife

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.FiniteT

/-- "`F = cdf μ` has a positive, differentiable density `F′ = f` for `t ≥ t₀`"
(Theorem 7, pp. 801–802): for every `t ≥ t₀`, `F` has derivative `f t` at `t` within
`[t₀, ∞)`, `f t > 0`, and `f` has derivative `f' t` at `t` within `[t₀, ∞)`. -/
def HasPosDiffDensity (μ : Measure ℝ) (t₀ : ℝ) (f f' : ℝ → ℝ) : Prop :=
  ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t ∧
    HasDerivWithinAt f (f' t) (Set.Ici t₀) t

/-- The norming function of Theorem 7 (p. 802): `a(t) = (1 - F(t)) / F′(t)` with
`F = cdf μ` and `F′ = f`. It is meaningful for `t ≥ t₀`, where `f t > 0`. -/
noncomputable def normA (μ : Measure ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 - cdf μ t) / f t

end BalkemaDeHaan.FiniteT
