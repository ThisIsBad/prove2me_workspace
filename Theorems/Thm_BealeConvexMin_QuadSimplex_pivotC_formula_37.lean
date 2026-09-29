import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 176, eq. (3.7) and the sentence after it. With `e = pivotE d p` (eq. (3.4))
and the new variable `z_q` stored in slot `p` (so the paper's `q` is `p` here and "`k, l ≠ q`"
reads "`k, l ≠ p`", index `0` included), the matrix `(c''_kl) = pivotC c p d` computed from (3.5)
and (3.6) satisfies (3.7); it is symmetric when `(c_kl)` is; and it is the transformed `(c_kl)`:
substituting `z_p = Σ_l e_l z'_l` into `C = Σ c_kl z_k z_l` gives `Σ c''_kl z'_k z'_l`. -/
theorem pivotC_formula_37 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p : Fin (N + 1))
    (d : Fin (N + 1) → ℝ) :
    let e := pivotE d p
    pivotC c p d p p = c p p * e p ^ 2 ∧
    (∀ l, l ≠ p → pivotC c p d p l = c p l * e p + c p p * e p * e l) ∧
    (∀ k, k ≠ p → pivotC c p d k p = c k p * e p + c p p * e k * e p) ∧
    (∀ k l, k ≠ p → l ≠ p →
      pivotC c p d k l = c k l + c k p * e l + c p l * e k + c p p * e k * e l) ∧
    (c.IsSymm → (pivotC c p d).IsSymm) ∧
    ∀ z' : Fin (N + 1) → ℝ,
      quadValue c (Function.update z' p (∑ l, e l * z' l)) = quadValue (pivotC c p d) z' := by sorry

end BealeConvexMin.QuadSimplex
