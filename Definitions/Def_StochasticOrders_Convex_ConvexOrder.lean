import Mathlib

namespace StochasticOrders.Convex

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The convex order `X ≤cx Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 109,
Eq. (3.A.1)): a random variable `X` on `(Ω, μ)` is smaller than a random variable `Y` on a
(possibly different) probability space `(Ω', ν)` in the convex order if `E[φ(X)] ≤ E[φ(Y)]` for
every convex function `φ : ℝ → ℝ` for which the two expectations exist. -/
def ConvexOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
    ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (Y ω) ∂ν

/-- The survival function `P{X > x}` of a random variable `X` on `(Ω, μ)`, as a real number
(Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 110, notation `F̄`); well-defined
in `[0,1]` for a probability measure, so the `ENNReal.toReal` cast loses no information. -/
noncomputable def tailProb (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  (μ {ω | x < X ω}).toReal

/-- The distribution function `P{X ≤ x}` of a random variable `X` on `(Ω, μ)`, as a real number
(Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 110, notation `F`). -/
noncomputable def cdf (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  (μ {ω | X ω ≤ x}).toReal

end StochasticOrders.Convex
