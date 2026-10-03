import Mathlib

open scoped ENNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), p. 205: the geometric distribution `geo(μ)` of the number `Y` of independent
Bernoulli trials with success probability `μ` up to and including the first success:
`P(Y = y) = μ (1 - μ)^{y-1}` for `y ≥ 1`, and `0` at `y = 0`. Intended for `0 < μ < 1`. -/
noncomputable def geomTrials (μ : ℝ) (y : ℕ) : ℝ≥0∞ :=
  if 1 ≤ y then ENNReal.ofReal (μ * (1 - μ) ^ (y - 1)) else 0

/-- Sennott (1999), pp. 205–206: the negative binomial distribution `neg bin(μ, r)` of the number
`Y` of independent Bernoulli trials with success probability `μ` until exactly `r` successes are
achieved: `P(Y = y) = C(y-1, r-1) μ^r (1 - μ)^{y-r}` for `y ≥ r`, and `0` for `y < r`.
Intended for `0 < μ < 1` and `r ≥ 1`. -/
noncomputable def negBinTrials (μ : ℝ) (r : ℕ) (y : ℕ) : ℝ≥0∞ :=
  if r ≤ y then ENNReal.ofReal ((Nat.choose (y - 1) (r - 1) : ℝ) * μ ^ r * (1 - μ) ^ (y - r))
  else 0

/-- Sennott (1999), (9.1) and (9.14), p. 206: the truncated Poisson distribution `trun Pois(λ)`,
`P(Y = y) = (e^{-λ} / (1 - e^{-λ})) λ^y / y!` for `y ≥ 1`, and `0` at `y = 0`.
Intended for `λ > 0`. -/
noncomputable def truncPoisson (lam : ℝ) (y : ℕ) : ℝ≥0∞ :=
  if 1 ≤ y then
    ENNReal.ofReal (Real.exp (-lam) / (1 - Real.exp (-lam)) * lam ^ y / (y.factorial : ℝ))
  else 0

end SennottDP.ResidualLife
