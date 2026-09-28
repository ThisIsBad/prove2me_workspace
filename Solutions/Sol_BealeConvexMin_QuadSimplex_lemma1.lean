import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC

namespace BealeConvexMin.QuadSimplex

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem solution {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hc : c.IsSymm)
    (p : Fin (N + 1)) (hp : c p p ≠ 0) :
    pivotE (c p) p p = 1 / c p p ∧
    (∀ l, l ≠ p → pivotE (c p) p l = -c p l / c p p) ∧
    ∀ k, k ≠ p → pivotC c p (c p) p k = 0 ∧ pivotC c p (c p) k p = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pivotE]
  · intro l hl
    simp [pivotE, hl]
  · intro k hk
    have hsym : c k p = c p k := by
      have := congrFun (congrFun hc p) k
      simpa [Matrix.transpose_apply] using this
    refine ⟨?_, ?_⟩
    · simp only [pivotC, pivotCPrime, pivotE, Matrix.of_apply, if_true, hk, if_false]
      field_simp
      ring
    · simp only [pivotC, pivotCPrime, pivotE, Matrix.of_apply, if_true, hk, if_false]
      rw [hsym]
      field_simp
      ring
