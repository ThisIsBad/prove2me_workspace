import Mathlib

namespace FreedmanTail.Laplace

/-- Freedman (1975), Definition (1.2)(b), p. 101: `f(λ) = e^{−λ} − 1 + λ`. -/
noncomputable def f (lam : ℝ) : ℝ := Real.exp (-lam) - 1 + lam

/-- Freedman (1975), Definition (1.2)(e), p. 101: `R_λ(v, y) = exp{λy − f(λ)v}`.
The page prints `exp{λh − f(λ)v}`; `h` is a misprint for `y` (compare (1.3)(d) and (3.6)).
The time variable `v` comes first, the space variable `y` second. -/
noncomputable def R (lam v y : ℝ) : ℝ := Real.exp (lam * y - f lam * v)

end FreedmanTail.Laplace
