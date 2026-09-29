import Mathlib

namespace StochasticOrders.MonotoneConvex

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The increasing convex order `X ≤icx Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer
2007, p. 181, Eq. (4.A.1), increasing-convex case): a random variable `X` on `(Ω, μ)` is smaller
than a random variable `Y` on a (possibly different) probability space `(Ω', ν)` in the increasing
convex order if `E[φ(X)] ≤ E[φ(Y)]` for every increasing convex function `φ : ℝ → ℝ` for which the
two expectations exist. -/
def IcxOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Monotone φ → ConvexOn ℝ Set.univ φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
    ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

/-- The upper tail integral `∫_x^∞ F̄(u) du` of a random variable `X` on `(Ω, μ)` (Shaked &
Shanthikumar, *Stochastic Orders*, Springer 2007, p. 182, Eq. (4.A.5)), the alternative,
integration-by-parts form of `E[(X-x)^+]` (Eq. (4.A.4)) that Theorem 4.A.2 characterizes `≤icx`
with. -/
noncomputable def tailUpperIntegral (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  ∫ u in Set.Ici x, (μ {ω | u < X ω}).toReal

end StochasticOrders.MonotoneConvex
