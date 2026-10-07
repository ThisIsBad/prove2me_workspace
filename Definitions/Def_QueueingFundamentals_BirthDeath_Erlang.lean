import Mathlib

namespace QueueingFundamentals.BirthDeath

/-- The Erlang-B (Erlang loss) formula (2.53), p.82:
`B(c, r) = (r^c / c!) / ∑_{i=0}^{c} r^i / i!`. -/
noncomputable def erlangB (c : ℕ) (r : ℝ) : ℝ :=
  (r ^ c / (c.factorial : ℝ)) / ∑ i ∈ Finset.range (c + 1), r ^ i / (i.factorial : ℝ)

/-- The Erlang-C formula (2.38), p.69, with `ρ = r / c`:
`C(c, r) = (r^c / (c!(1 − ρ))) / (r^c / (c!(1 − ρ)) + ∑_{n=0}^{c-1} r^n / n!)`.
The book defines it for `r < c` (`ρ < 1`); outside that range the expression has no meaning,
and every statement using it assumes `0 < r < c`. -/
noncomputable def erlangC (c : ℕ) (r : ℝ) : ℝ :=
  (r ^ c / ((c.factorial : ℝ) * (1 - r / c))) /
    (r ^ c / ((c.factorial : ℝ) * (1 - r / c)) +
      ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ))

/-- The right-hand side of (2.44), p.75: `α(β) = φ(β) / (φ(β) + β Φ(β))`, where `φ` and `Φ` are
the PDF and the CDF of a standard normal random variable. -/
noncomputable def halfinWhittAlpha (β : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 1 β /
    (ProbabilityTheory.gaussianPDFReal 0 1 β +
      β * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) β)

end QueueingFundamentals.BirthDeath
