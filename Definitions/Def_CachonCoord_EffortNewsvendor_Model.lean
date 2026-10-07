import Mathlib

namespace CachonCoord.EffortNewsvendor

open MeasureTheory ProbabilityTheory

/-- The newsvendor with effort-dependent demand of §6.4.1 (Cachon 2003, 3rd draft, pp. 41–42),
with the chapter's standing assumptions of §6.2.1 (p. 7) and the zeros `g_r = g_s = 0`, `v = 0`,
`c_r = 0` of p. 41. Effort levels are `e ≥ 0`.

* `p` is the retail price and `c` (`= c_s`, since `c_r = 0`) the unit production cost, `0 ≤ c < p`.
* `law e` is the law of demand given effort `e`, a probability measure on `[0, ∞)` with finite
  mean, whose distribution function `F(·|e) = cdf (law e)` is continuous at `0` (`F(0|e) = 0`) and
  strictly increasing on `[0, ∞)`.
* `effortSlope y e` is `∂F(y|e)/∂e`, negative for `y > 0` and `e > 0`
  ("demand is stochastically increasing in effort").
* `effortCost` is the book's `g(e)`, with `g(0) = 0`, `g′(e) > 0`, `g″(e) > 0`. -/
structure Model where
  /-- Retail price `p`. -/
  p : ℝ
  /-- Unit production cost `c`. -/
  c : ℝ
  c_nonneg : 0 ≤ c
  c_lt_p : c < p
  /-- Demand law given effort `e`. -/
  law : ℝ → Measure ℝ
  isProb : ∀ e : ℝ, 0 ≤ e → IsProbabilityMeasure (law e)
  nonneg : ∀ e : ℝ, 0 ≤ e → law e (Set.Iio 0) = 0
  no_atom_zero : ∀ e : ℝ, 0 ≤ e → law e {0} = 0
  finite_mean : ∀ e : ℝ, 0 ≤ e → Integrable (fun d : ℝ => d) (law e)
  cdf_strictMono : ∀ e : ℝ, 0 ≤ e → StrictMonoOn (fun y => cdf (law e) y) (Set.Ici 0)
  /-- `∂F(y|e)/∂e`. -/
  effortSlope : ℝ → ℝ → ℝ
  hasDerivAt_cdf : ∀ y e : ℝ, 0 < e →
    HasDerivAt (fun t => cdf (law t) y) (effortSlope y e) e
  effortSlope_neg : ∀ y e : ℝ, 0 < y → 0 < e → effortSlope y e < 0
  effortSlope_intervalIntegrable : ∀ e : ℝ, 0 < e → ∀ a b : ℝ,
    IntervalIntegrable (fun y => effortSlope y e) volume a b
  /-- Differentiation under the integral sign: `∂/∂e ∫_a^b F(y|e) dy = ∫_a^b ∂F(y|e)/∂e dy`. -/
  hasDerivAt_integral_cdf : ∀ e : ℝ, 0 < e → ∀ a b : ℝ,
    HasDerivAt (fun t => ∫ y in a..b, cdf (law t) y) (∫ y in a..b, effortSlope y e) e
  /-- The effort cost `g(e)`. -/
  effortCost : ℝ → ℝ
  /-- `g′(e)`. -/
  effortCost' : ℝ → ℝ
  /-- `g″(e)`. -/
  effortCost'' : ℝ → ℝ
  effortCost_zero : effortCost 0 = 0
  effortCost_continuousOn : ContinuousOn effortCost (Set.Ici 0)
  hasDerivAt_effortCost : ∀ e : ℝ, 0 < e → HasDerivAt effortCost (effortCost' e) e
  hasDerivAt_effortCost' : ∀ e : ℝ, 0 < e → HasDerivAt effortCost' (effortCost'' e) e
  effortCost'_pos : ∀ e : ℝ, 0 < e → 0 < effortCost' e
  effortCost''_pos : ∀ e : ℝ, 0 < e → 0 < effortCost'' e

namespace Model

variable (M : Model)

/-- `F(y|e)`, the distribution function of demand given effort `e`. -/
noncomputable def F (y e : ℝ) : ℝ := cdf (M.law e) y

/-- Expected sales `S(q, e) = E[min(q, D)]` with `D ∼ F(·|e)` (p. 41). -/
noncomputable def S (q e : ℝ) : ℝ := ∫ d, min q d ∂(M.law e)

/-- The integrated channel's profit `Π(q, e) = pS(q, e) − cq − g(e)` (p. 41). -/
noncomputable def Pi (q e : ℝ) : ℝ := M.p * M.S q e - M.c * q - M.effortCost e

end Model

end CachonCoord.EffortNewsvendor
