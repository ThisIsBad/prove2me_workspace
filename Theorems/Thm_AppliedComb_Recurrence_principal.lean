import Mathlib
import Definitions.Def_AppliedComb_Recurrence_advance

namespace AppliedComb.Recurrence

/-- Keller–Trotter, Theorem 9.18 (p. 199), the Principal Theorem. Let `k` be a positive integer
and let `c₀, c₁, …, c_k` be real constants with `c₀ ≠ 0` and `c_k ≠ 0`. Then the set `W` of all
solutions `f : ℤ → ℝ` of the homogeneous equation `(c₀ A^k + c₁ A^(k-1) + ⋯ + c_k) f = 0` (9.5.1)
is a `k`-dimensional subspace of `V = (ℤ → ℝ)`: its dimension (`Module.rank`, a cardinal, so
an infinite-dimensional `W` would not satisfy the statement) equals `k`. -/
theorem principal (k : ℕ) (hk : 0 < k) (c : Fin (k + 1) → ℝ) (hc0 : c 0 ≠ 0)
    (hck : c (Fin.last k) ≠ 0) :
    Module.rank ℝ (solutionSpace k c) = k := by sorry

end AppliedComb.Recurrence

