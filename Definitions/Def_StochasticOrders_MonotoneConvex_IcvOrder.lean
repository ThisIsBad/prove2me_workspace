import Mathlib

namespace StochasticOrders.MonotoneConvex

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The increasing concave order `X ≤icv Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer
2007, p. 181, Eq. (4.A.1), increasing-concave case): a random variable `X` on `(Ω, μ)` is smaller
than a random variable `Y` on a (possibly different) probability space `(Ω', ν)` in the increasing
concave order if `E[φ(X)] ≤ E[φ(Y)]` for every increasing concave function `φ : ℝ → ℝ` for which
the two expectations exist. -/
def IcvOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Monotone φ → ConcaveOn ℝ Set.univ φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
    ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

/-- The lower tail integral `∫_{-∞}^x F(u) du` of a random variable `X` on `(Ω, μ)` (Shaked &
Shanthikumar, *Stochastic Orders*, Springer 2007, p. 182, Eq. (4.A.7)), the alternative,
integration-by-parts form of `E[(X-x)^-]` (Eq. (4.A.6)) that Theorem 4.A.2 characterizes `≤icv`
with. -/
noncomputable def tailLowerIntegral (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  ∫ u in Set.Iic x, (μ {ω | X ω ≤ u}).toReal

end StochasticOrders.MonotoneConvex
