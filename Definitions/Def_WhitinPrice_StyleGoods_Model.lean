import Mathlib

namespace WhitinPrice.StyleGoods

open MeasureTheory ProbabilityTheory

/-- Mean demand at unit profit `P` (Whitin 1955, §3, p. 66): the line relating unit profit and
amount demanded, with reciprocal slope `k` and zero demand at `P = P₀`, i.e. `μ(P) = k (P − P₀)`.
It is positive for `P < P₀` exactly when `k < 0`. -/
noncomputable def meanDemand (k P₀ P : ℝ) : ℝ := k * (P - P₀)

/-- The demand law at unit profit `P` (§3, p. 66): the rectangular (uniform) distribution on the
interval from `0` to twice mean demand, `[0, 2 μ(P)]`, i.e. Lebesgue measure conditioned on that
interval. (When `2 μ(P) ≤ 0` the interval is null and this is the zero measure; every theorem
assumes `k < 0` and `P < P₀`.) -/
noncomputable def demandLaw (k P₀ P : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc 0 (2 * meanDemand k P₀ P))

/-- `f(x)` (§3, p. 64): the probability of selling the marginal (`x`-th) unit, i.e. that demand
is at least `x`, weighted by the unit profit `P`. -/
noncomputable def marginalProfit (k P₀ P x : ℝ) : ℝ :=
  P * (demandLaw k P₀ P).real (Set.Ici x)

/-- `g(x)` (§3, p. 64): the probability of not selling the marginal (`x`-th) unit, i.e. that
demand is less than `x`, weighted by the unit liquidation loss `L`. -/
noncomputable def marginalLoss (k P₀ L P x : ℝ) : ℝ :=
  L * (demandLaw k P₀ P).real (Set.Iio x)

/-- Expected profit `E(P, x)` of stocking `x` units at unit profit `P` (§3, Eq. (10), p. 66):
`∫₀ˣ [f(t) − g(t)] dt`, the expected profit on sales minus the expected liquidation loss. -/
noncomputable def expectedProfit (k P₀ L P x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, (marginalProfit k P₀ P t - marginalLoss k P₀ L P t)

/-- The equilibrium stock `x_M(P, L) = −2kP(P₀ − P)/(P + L)` of Eq. (12), p. 66. -/
noncomputable def optimalStock (k P₀ L P : ℝ) : ℝ :=
  -(2 * k * P * (P₀ - P)) / (P + L)

end WhitinPrice.StyleGoods
