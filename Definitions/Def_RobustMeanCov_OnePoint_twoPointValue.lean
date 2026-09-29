import Mathlib

namespace RobustMeanCov.OnePoint

/-- `U(p, x)` of (8) (Popescu 2007, p. 101) with `μ_x = m`, `σ_x = s`: the expected utility
`E[u(r_p)]` of the two-point law with mass `p` at `m + √((1-p)/p)·s` and mass `1 - p` at
`m - √(p/(1-p))·s`. Only meaningful for `p ∈ (0, 1)`; every statement restricts `p` to that
interval or approaches its endpoints from inside. -/
noncomputable def twoPointValue (u : ℝ → ℝ) (m s p : ℝ) : ℝ :=
  p * u (m + Real.sqrt ((1 - p) / p) * s) + (1 - p) * u (m - Real.sqrt (p / (1 - p)) * s)

end RobustMeanCov.OnePoint
