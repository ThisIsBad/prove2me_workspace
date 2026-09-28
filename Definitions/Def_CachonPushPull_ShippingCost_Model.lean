import Mathlib

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- The standing demand assumptions of Cachon (2004), §3, p. 225, for a demand law `μ` on `ℝ`
with distribution function `F = cdf μ` and a density `f`:
* `F(0) = 0` (there is always some demand);
* `F` is strictly increasing on `[0, ∞)`;
* `f` is the derivative of `F` at every `x > 0`;
* IGFR: the generalized failure rate `g(x) = x f(x) / (1 - F(x))` has `g'(x) > 0` for `x > 0`
  (a positive derivative forces `g` to be differentiable there).
Differentiability is required on `(0, ∞)` only, so the exponential law (kink at `0`), which the
paper names as IGFR, is admitted. -/
structure DemandModel (μ : Measure ℝ) (f : ℝ → ℝ) : Prop where
  cdf_zero : cdf μ 0 = 0
  strictMonoOn : StrictMonoOn (cdf μ) (Set.Ici 0)
  hasDerivAt : ∀ x : ℝ, 0 < x → HasDerivAt (cdf μ) (f x) x
  igfr : ∀ x : ℝ, 0 < x → 0 < deriv (fun y : ℝ => y * f y / (1 - cdf μ y)) x

/-- Expected sales `S(q) = q - ∫₀^q F(x) dx` (Eq. (1), p. 226). -/
noncomputable def S (μ : Measure ℝ) (q : ℝ) : ℝ :=
  q - ∫ x in (0 : ℝ)..q, cdf μ x

end CachonPushPull.ShippingCost
