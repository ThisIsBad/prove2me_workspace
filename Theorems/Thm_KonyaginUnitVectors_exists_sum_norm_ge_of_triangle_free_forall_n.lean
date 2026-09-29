import Mathlib
open scoped RealInnerProductSpace

namespace KonyaginUnitVectors

theorem exists_sum_norm_ge_of_triangle_free_forall_n :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      ∃ (d : ℕ) (u : Fin n → EuclideanSpace ℝ (Fin d)),
        (∀ i, ‖u i‖ = 1) ∧
        (∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
          ⟪u i, u j⟫ = 0 ∨ ⟪u j, u k⟫ = 0 ∨ ⟪u i, u k⟫ = 0) ∧
        c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ ‖∑ i, u i‖ := by sorry

end KonyaginUnitVectors
