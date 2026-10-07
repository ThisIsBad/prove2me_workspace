import Mathlib

namespace QueueingFundamentals.Foundations

/-- p.22: with a time-dependent rate `λ(t)`, the unique solution of the forward equations
with `p_0(0) = 1`, `p_n(0) = 0` (`n > 0`) is the nonhomogeneous Poisson law
`p_n(t) = e^{-m(t)} m(t)^n / n!`, `m(t) = ∫_0^t λ(s) ds`. -/
theorem nonhomogeneous_poisson (lam : ℝ → ℝ) (hcont : ContinuousOn lam (Set.Ici 0))
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ lam t) (p : ℕ → ℝ → ℝ) :
    ((∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (p 0) (-lam t * p 0 t) (Set.Ici 0) t) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt (p n) (-lam t * p n t + lam t * p (n - 1) t) (Set.Ici 0) t) ∧
      p 0 0 = 1 ∧ (∀ n : ℕ, 0 < n → p n 0 = 0)) ↔
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      p n t = Real.exp (-(∫ s in (0 : ℝ)..t, lam s)) * (∫ s in (0 : ℝ)..t, lam s) ^ n /
        (n.factorial : ℝ) := by sorry

end QueueingFundamentals.Foundations

