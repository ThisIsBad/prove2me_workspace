import Mathlib

namespace PhiDivRobust.Barrier

/-- The perspective `g(s, y) = y f(s / y)` of `f : ℝ → ℝ` (proof of Theorem 2, Ben-Tal et al. 2013,
p. 350). The first coordinate is `s`, the second is `y`. -/
noncomputable def perspective (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2 * f (p.1 / p.2)

end PhiDivRobust.Barrier
