import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents

namespace FreedmanTail.Bernstein

/-- Freedman (1975), proof of (4.1) Theorem, p. 108: for positive `a, b`, the λ ≥ 0 minimizing
`exp[−λa + e(λ)b]` is `λ₀ = log[(a + b)/b]`, and the minimum is `(b/(a+b))^{a+b} e^a`. -/
theorem minimizing_lambda (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ Real.log ((a + b) / b) ∧
      (∀ lam : ℝ, 0 ≤ lam →
        Real.exp (-Real.log ((a + b) / b) * a + e (Real.log ((a + b) / b)) * b)
          ≤ Real.exp (-lam * a + e lam * b)) ∧
      Real.exp (-Real.log ((a + b) / b) * a + e (Real.log ((a + b) / b)) * b)
        = (b / (a + b)) ^ (a + b) * Real.exp a := by sorry

end FreedmanTail.Bernstein

