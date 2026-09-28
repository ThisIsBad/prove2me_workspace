import Mathlib

namespace OnlinePrimalDual.BoundedAllocation

/-- The allocation algorithm's competitive ratio, `C(d) = 1 - (d-1)/(d(1+1/(d-1))^(d-1))`
(Buchbinder & Naor, FnT TCS 2009, Theorem 13.1, p. 240), taken verbatim from the book's own
closed form. -/
noncomputable def competitiveRatio (d : ℕ) : ℝ :=
  1 - ((d : ℝ) - 1) / ((d : ℝ) * (1 + 1 / ((d : ℝ) - 1)) ^ (d - 1))

end OnlinePrimalDual.BoundedAllocation
