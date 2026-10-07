import Mathlib

namespace QueueingFundamentals.Transient

/-- The M/M/∞ transient probabilities of p.101 for `N(0) = 0`:
`p_n(t) = (1/n!) ((1 - e^{-μt}) λ/μ)^n exp(-(1 - e^{-μt}) λ/μ)`. -/
noncomputable def mmInfTransient (lam mu : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((1 - Real.exp (-mu * t)) * (lam / mu)) ^ n / (Nat.factorial n : ℝ)
    * Real.exp (-((1 - Real.exp (-mu * t)) * (lam / mu)))

end QueueingFundamentals.Transient
