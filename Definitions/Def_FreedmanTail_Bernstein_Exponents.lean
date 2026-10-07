import Mathlib

namespace FreedmanTail.Bernstein

/-- Freedman (1975), Definition (1.2)(a), p. 101: `e(λ) = e^λ − 1 − λ`. -/
noncomputable def e (lam : ℝ) : ℝ := Real.exp lam - 1 - lam

/-- Freedman (1975), Definition (1.2)(d), p. 101: `Q_λ(v, y) = exp{λy − e(λ)v}`.
The time variable `v` comes first, the space variable `y` second. -/
noncomputable def Q (lam v y : ℝ) : ℝ := Real.exp (lam * y - e lam * v)

end FreedmanTail.Bernstein
