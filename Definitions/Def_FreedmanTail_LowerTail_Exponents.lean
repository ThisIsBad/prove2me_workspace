import Mathlib

namespace FreedmanTail.LowerTail

/-- Freedman (1975), Definition (1.2)(a), p. 101: `e(λ) = e^λ − 1 − λ`. -/
noncomputable def e (lam : ℝ) : ℝ := Real.exp lam - 1 - lam

/-- Freedman (1975), Definition (1.2)(b), p. 101: `f(λ) = e^{−λ} − 1 + λ`. -/
noncomputable def f (lam : ℝ) : ℝ := Real.exp (-lam) - 1 + lam

end FreedmanTail.LowerTail
