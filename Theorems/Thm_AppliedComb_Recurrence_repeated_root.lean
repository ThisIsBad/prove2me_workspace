import Mathlib
import Definitions.Def_AppliedComb_Recurrence_advance

namespace AppliedComb.Recurrence

/-- Keller–Trotter, Lemma 9.22 (p. 201). Let `k ≥ 1` and `r ≠ 0` (the standing assumption of
Section 9.5.2, p. 200: the book's lemma is stated for a root `r` of an equation `(A − r) f = 0`
with `r ≠ 0`). Then the general solution `f : ℤ → ℝ` of `(A − r)^k f = 0` (9.5.7) is
`f(n) = c₁ rⁿ + c₂ n rⁿ + c₃ n² rⁿ + ⋯ + c_k n^(k-1) rⁿ` (9.5.8): a function solves (9.5.7) if and
only if it has this form for some real constants `c₁, …, c_k` (here `c i` for `i : Fin k`
multiplies `n^i rⁿ`, so `c 0` is the book's `c₁`). -/
theorem repeated_root (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr : r ≠ 0) (f : ℤ → ℝ) :
    ((advance - r • (1 : Module.End ℝ (ℤ → ℝ))) ^ k) f = 0 ↔
      ∃ c : Fin k → ℝ, ∀ n : ℤ, f n = ∑ i : Fin k, c i * (n : ℝ) ^ (i : ℕ) * r ^ n := by sorry

end AppliedComb.Recurrence

