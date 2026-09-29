import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar

open scoped InnerProductSpace

namespace ConeLifts.Factorization

/-- Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Theorem 2.4, proof, p. 4: for an extreme point
`c` of `C°`, `max{⟨c, x⟩ : x ∈ C} = 1` (the maximum is attained). The hypothesis `1 ≤ n` is the
paper's implicit "full-dimensional convex body in ℝⁿ"; for `n = 0` the maximum is `0`. -/
theorem extremePoint_polar_isGreatest {n : ℕ} (hn : 1 ≤ n)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C)) :
    IsGreatest ((fun x => ⟪c, x⟫_ℝ) '' C) 1 := by sorry

end ConeLifts.Factorization
