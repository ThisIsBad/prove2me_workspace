import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177, Lemma 2. Let the new nonbasic variable be the free variable of (3.2)
(coefficients `d = c p`, row `p` of `c`, with `c_pp ≠ 0`), and let `l ≠ p` be a slot whose row and
column of `(c_kl)` vanish off the diagonal: `c_kl = c_lk = 0` for all `k ≠ l` (index `0` included).
Then `e_l = 0`, and the new matrix keeps the property: `c''_kl = c''_lk = 0` for all `k ≠ l`. -/
theorem lemma2 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p l : Fin (N + 1))
    (hp : c p p ≠ 0) (hlp : l ≠ p) (hl : ∀ k, k ≠ l → c k l = 0 ∧ c l k = 0) :
    pivotE (c p) p l = 0 ∧
    ∀ k, k ≠ l → pivotC c p (c p) k l = 0 ∧ pivotC c p (c p) l k = 0 := by sorry

end BealeConvexMin.QuadSimplex
