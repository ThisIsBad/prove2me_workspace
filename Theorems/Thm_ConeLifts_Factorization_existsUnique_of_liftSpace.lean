import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone
import Definitions.Def_ConeLifts_Shared_dualCone

open scoped InnerProductSpace

namespace ConeLifts.Factorization

/-- Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Theorem 2.4, proof, p. 5: let
`B : ext(C°) → K*` and `L = {(x, z) : 1 - ⟨x, y⟩ = ⟨z, B(y)⟩ ∀ y ∈ ext(C°)}`. For each
`z ∈ K ∩ L_K` (i.e. `z ∈ K` with `(x, z) ∈ L` for some `x`) there is a unique `x_z ∈ ℝⁿ` with
`(x_z, z) ∈ L`. -/
theorem existsUnique_of_liftSpace {n m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hB : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), B y ∈ ConeLifts.Shared.dualCone K)
    (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ K)
    (hzL : ∃ x : EuclideanSpace ℝ (Fin n),
      ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ) :
    ∃! x : EuclideanSpace ℝ (Fin n),
      ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ := by sorry

end ConeLifts.Factorization
