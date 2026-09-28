import Mathlib

namespace StochasticOrders.MeanResidualLife

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The survival function `P{X > x}` of a random variable `X` on `(Ω, μ)` (Shaked & Shanthikumar,
*Stochastic Orders*, Springer 2007, p. 16, notation `F̄`), restated locally since this chapter's
mission cannot import Chunk 01's `Definitions.Def_StochasticOrders_Usual_HazardRateOrder`. -/
noncomputable def survival (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ENNReal :=
  μ {ω | x < X ω}

/-- The hazard rate order `X ≤hr Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007,
p. 16, Eq. (1.B.4)), restated locally (see `survival` above): the general equivalent condition,
valid without assuming absolute continuity, that the survival functions `F̄` of `X` and `Ḡ` of `Y`
satisfy `F̄(x) Ḡ(y) ≥ F̄(y) Ḡ(x)` for all `x ≤ y`. -/
def HazardRateOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ x y : ℝ, x ≤ y → survival μ X y * survival ν Y x ≤ survival μ X x * survival ν Y y

end StochasticOrders.MeanResidualLife
