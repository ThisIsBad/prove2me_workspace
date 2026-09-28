import Mathlib
import Definitions.Def_LimitedBFGS_SQN_sqnIter

open Matrix

namespace LimitedBFGS.SQN

/-- Section 3, p. 778 ("Hence, it has quadratic termination"): the SQN method (17) with `m ≥ 1`
stored corrections, a positive definite initial matrix `H₀` and exact line searches, applied to
the strictly convex quadratic `f(x) = ½ xᵀAx + bᵀx` on `ℝⁿ`, reaches the minimizer, i.e. an
iterate with `A x_k + b = 0`, after at most `n` steps. -/
theorem sqn_quadratic_termination {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (m : ℕ) (hm : 1 ≤ m)
    (x₀ : Fin n → ℝ) :
    ∃ k ≤ n, grad A b (sqnIter A b H₀ m x₀ k).x = 0 := by sorry

end LimitedBFGS.SQN

