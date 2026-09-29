import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar

open scoped InnerProductSpace

namespace ConeLifts.Factorization

/-- Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Theorem 2.4, proof, p. 5: for any map
`B : ext(C°) → ℝᵐ`, the coordinate projection `L_K` to `ℝᵐ` of the affine space
`L = {(x, z) ∈ ℝⁿ × ℝᵐ : 1 - ⟨x, y⟩ = ⟨z, B(y)⟩ ∀ y ∈ ext(C°)}` does not contain the origin. -/
theorem zero_not_mem_liftSpace {n m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    (0 : EuclideanSpace ℝ (Fin m)) ∉
      {z : EuclideanSpace ℝ (Fin m) | ∃ x : EuclideanSpace ℝ (Fin n),
        ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ} := by sorry

end ConeLifts.Factorization
