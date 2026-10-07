import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_besselI

namespace QueueingFundamentals.Transient

/-- The right-hand side of (2.75): the probability that the M/M/1 queue started with `N(0) = i`
has `n` customers at time `t`, with `ρ = λ/μ` and `y = 2t√(λμ)`:
`p_n(t) = e^{-(λ+μ)t} [ ρ^{(n-i)/2} I_{n-i}(y) + ρ^{(n-i-1)/2} I_{n+i+1}(y)
  + (1-ρ) ρ^n ∑_{j ≥ n+i+2} ρ^{-j/2} I_j(y) ]`.
Powers of `ρ` with half-integer exponents are real powers (`ρ > 0` when `λ > 0`), and
`I_{n-i}` uses `I_{-m} = I_m`. -/
noncomputable def mm1Transient (lam mu : ℝ) (i n : ℕ) (t : ℝ) : ℝ :=
  let ρ : ℝ := lam / mu
  let y : ℝ := 2 * t * Real.sqrt (lam * mu)
  Real.exp (-(lam + mu) * t) *
    (ρ ^ (((n : ℝ) - (i : ℝ)) / 2) * besselIZ ((n : ℤ) - (i : ℤ)) y
      + ρ ^ (((n : ℝ) - (i : ℝ) - 1) / 2) * besselI (n + i + 1) y
      + (1 - ρ) * ρ ^ n *
          ∑' j : ℕ, ρ ^ (-(((j + n + i + 2 : ℕ) : ℝ)) / 2) * besselI (j + n + i + 2) y)

end QueueingFundamentals.Transient
