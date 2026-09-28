import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl

namespace StochasticOrders.MeanResidualLife

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The mean residual life order `X ≤mrl Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer
2007, p. 82, Eq. (2.A.2)): a random variable `X` on `(Ω, μ)` with mrl function `m` is smaller than
a random variable `Y` on a (possibly different) probability space `(Ω', ν)` with mrl function `l`
in the mean residual life order if `m(t) ≤ l(t)` for every real `t`. -/
def MrlOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ t : ℝ, mrl μ X t ≤ mrl ν Y t

end StochasticOrders.MeanResidualLife
