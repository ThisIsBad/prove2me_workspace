import Mathlib

namespace CachonCoord.Proportional

open MeasureTheory ProbabilityTheory

/-- The newsvendor data of §6.5.1 (Cachon 2003, 3rd draft, pp. 48–50), with the chapter's
standing assumptions of §6.2.1 (p. 7) and the zeros `c_r = g_r = g_s = v = 0` of p. 48.

* `law` is the law of the total retail demand `D`: a probability measure on `[0, ∞)` with finite
  mean; its distribution function `F = cdf law` satisfies `F(0) = 0`, is strictly increasing on
  `[0, ∞)`, and is differentiable at every `y > 0` with derivative `density y` (the book's `f`).
* `p` is the retail price and `c` (`= c_s`, since `c_r = 0`) the supplier's unit production
  cost, with `0 < c < p`. -/
structure Model where
  /-- Law of the total retail demand `D`. -/
  law : Measure ℝ
  isProb : IsProbabilityMeasure law
  nonneg : law (Set.Iio 0) = 0
  integrable : Integrable (fun d : ℝ => d) law
  /-- `F(0) = 0`. -/
  cdf_zero : cdf law 0 = 0
  /-- `F` is strictly increasing on `[0, ∞)`. -/
  strictMonoOn_cdf : StrictMonoOn (cdf law) (Set.Ici 0)
  /-- The density `f`. -/
  density : ℝ → ℝ
  /-- `F` is differentiable on `(0, ∞)` with derivative `f`. -/
  hasDerivAt_cdf : ∀ y : ℝ, 0 < y → HasDerivAt (cdf law) (density y) y
  /-- Retail price `p`. -/
  p : ℝ
  /-- Unit production cost `c`. -/
  c : ℝ
  c_pos : 0 < c
  c_lt_p : c < p

namespace Model

variable (M : Model)

/-- The distribution function `F` of total demand. -/
noncomputable def F (y : ℝ) : ℝ := cdf M.law y

/-- Expected sales `S(q) = E[min(q, D)]` (p. 10). -/
noncomputable def S (q : ℝ) : ℝ := ∫ d, min q d ∂M.law

/-- Expected leftover inventory `I(q) = E[(q − D)⁺]` (p. 10). -/
noncomputable def I (q : ℝ) : ℝ := ∫ d, max (q - d) 0 ∂M.law

/-- The integrated supply chain's expected profit `Π(q) = pS(q) − cq` at total stock `q`. -/
noncomputable def chainProfit (q : ℝ) : ℝ := M.p * M.S q - M.c * q

/-- The average of `F` over `[0, q]`, `(1/q) ∫_0^q F(x) dx` (meaningful for `q > 0`). -/
noncomputable def avgF (q : ℝ) : ℝ := (1 / q) * ∫ x in (0 : ℝ)..q, M.F x

end Model

end CachonCoord.Proportional
