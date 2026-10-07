import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

open MeasureTheory

/-- The model of §6.9.1 (Cachon 2003, 3rd draft, p. 92), after Kouvelis and Lariviere (2000).
The production manager chooses an input level `e ≥ 0`, which yields the output `Q = Y e`, where
`Y ∈ [0, 1]` is random; he incurs the cost `c(e)`, strictly convex and increasing. Retailer `i`
observes the realization `αᵢ` of the random variable `Aᵢ > 0`. The constant demand elasticity is
`η > 1`. The random variables live on a probability space `(Ω, P)`; `c'` is the derivative of `c`
on `(0, ∞)`. -/
structure Model (Ω : Type*) [MeasurableSpace Ω] where
  /-- The constant demand elasticity `η`. -/
  η : ℝ
  /-- `η > 1`. -/
  one_lt_η : 1 < η
  /-- The probability measure. -/
  P : Measure Ω
  /-- `P` is a probability measure. -/
  isProb : IsProbabilityMeasure P
  /-- Retailer one's demand shock `A₁`. -/
  A₁ : Ω → ℝ
  /-- Retailer two's demand shock `A₂`. -/
  A₂ : Ω → ℝ
  /-- The output shock `Y`. -/
  Y : Ω → ℝ
  meas_A₁ : Measurable A₁
  meas_A₂ : Measurable A₂
  meas_Y : Measurable Y
  /-- `A₁ > 0`. -/
  A₁_pos : ∀ ω, 0 < A₁ ω
  /-- `A₂ > 0`. -/
  A₂_pos : ∀ ω, 0 < A₂ ω
  /-- `Y ∈ [0, 1]`. -/
  Y_mem : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1
  /-- The production manager's cost `c(e)`. -/
  c : ℝ → ℝ
  /-- The derivative `c'(e)` for `e > 0`. -/
  c' : ℝ → ℝ
  /-- `c` is strictly convex on `e ≥ 0`. -/
  c_strictConvex : StrictConvexOn ℝ (Set.Ici 0) c
  /-- `c` is increasing on `e ≥ 0`. -/
  c_mono : MonotoneOn c (Set.Ici 0)
  /-- `c` is differentiable at every `e > 0` with derivative `c'(e)`. -/
  c_hasDeriv : ∀ e : ℝ, 0 < e → HasDerivAt c (c' e) e

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)

/-- Total expected supply chain profit `Π(e, A, Y) = E[π(A, Ye)] − c(e)` (§6.9.1, p. 93), where
`π(α, Q)` is the retailers' revenue under the optimal allocation. -/
noncomputable def chainProfit (e : ℝ) : ℝ :=
  (∫ ω, optRevenue M.η (M.A₁ ω) (M.A₂ ω) (M.Y ω * e) ∂M.P) - M.c e

/-- The constant `K = E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}]` appearing in (45) and (46). -/
noncomputable def K : ℝ :=
  ∫ ω, (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) * M.Y ω ^ ((M.η - 1) / M.η) ∂M.P

/-- The per-unit payment to the production manager, the left side of (46) (§6.9.1, p. 94):
`((η − 1)/η) (e°)^{−1/η} E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}] / E[Y]`, for a target effort `e°`. -/
noncomputable def payRate (eo : ℝ) : ℝ :=
  ((M.η - 1) / M.η) * eo ^ (-1 / M.η) * M.K / ∫ ω, M.Y ω ∂M.P

/-- Expected output `E[Q | e] = E[Y e]`. -/
noncomputable def expOutput (e : ℝ) : ℝ :=
  ∫ ω, M.Y ω * e ∂M.P

/-- The supplier's expected revenue from the internal market at effort `e`,
`E[Q w(A, Q) | e]` with `Q = Y e`: each realized unit is sold at the market price `w(A, Q)`. -/
noncomputable def expMarketRevenue (e : ℝ) : ℝ :=
  ∫ ω, (M.Y ω * e) * price M.η (M.A₁ ω) (M.A₂ ω) (M.Y ω * e) ∂M.P

/-- The production manager's expected utility at effort `e` when the supplier pays him the rate
(46) set for the target effort `e°` per unit of realized output (§6.9.1, p. 94):
`u(e) = payRate(e°) · E[Y e] − c(e)`. -/
noncomputable def managerUtility (eo e : ℝ) : ℝ :=
  M.payRate eo * M.expOutput e - M.c e

end Model

end CachonCoord.InternalMarket
