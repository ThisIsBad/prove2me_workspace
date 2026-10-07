import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents

namespace FreedmanTail.Bernstein

/-- Freedman (1975), (3.2) Corollary, p. 106: `exp(λx) ≤ 1 + λx + x² e(λ)` for `λ ≥ 0`, `x ≤ 1`. -/
theorem corollary_3_2 (lam x : ℝ) (hlam : 0 ≤ lam) (hx : x ≤ 1) :
    Real.exp (lam * x) ≤ 1 + lam * x + x ^ 2 * e lam := by sorry

end FreedmanTail.Bernstein

