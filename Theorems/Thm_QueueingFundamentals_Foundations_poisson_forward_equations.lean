import Mathlib

namespace QueueingFundamentals.Foundations

/-- Eqs. (1.11)–(1.14): the unique solution of the Poisson differential-difference equations
with `p_0(0) = 1`, `p_n(0) = 0` (`n > 0`) is `p_n(t) = (λt)^n e^{-λt} / n!` on `t ≥ 0`. -/
theorem poisson_forward_equations (lam : ℝ) (hlam : 0 < lam) (p : ℕ → ℝ → ℝ) :
    ((∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (p 0) (-lam * p 0 t) (Set.Ici 0) t) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt (p n) (-lam * p n t + lam * p (n - 1) t) (Set.Ici 0) t) ∧
      p 0 0 = 1 ∧ (∀ n : ℕ, 0 < n → p n 0 = 0)) ↔
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      p n t = (lam * t) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * t)) := by sorry

end QueueingFundamentals.Foundations

