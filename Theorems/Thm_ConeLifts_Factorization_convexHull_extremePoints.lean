import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar

namespace ConeLifts.Factorization

/-- Gouveia, Parrilo & Thomas, *Lifts of Convex Sets and Cone Factorizations*,
arXiv:1111.3164v2, §2, p. 3: "Since C is compact with the origin in its interior, both C and C°
are convex hulls of their respective extreme points." -/
theorem convexHull_extremePoints {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsConvexBody C) :
    C = convexHull ℝ (Set.extremePoints ℝ C) ∧
      ConeLifts.Shared.polar C = convexHull ℝ (Set.extremePoints ℝ (ConeLifts.Shared.polar C)) := by sorry

end ConeLifts.Factorization
