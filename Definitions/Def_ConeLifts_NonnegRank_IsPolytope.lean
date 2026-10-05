import Mathlib

open scoped InnerProductSpace

namespace ConeLifts.NonnegRank

/-- A **polytope** in the sense of Gouveia, Parrilo & Thomas, arXiv:1111.3164v2: a convex body
(§2, p. 3: compact, convex, with the origin in its interior — the paper's standing assumption
"throughout the paper") that is the convex hull of a finite set of points of `ℝⁿ`
(`EuclideanSpace ℝ (Fin n)`). Compactness and convexity follow from being the convex hull of a finite
set; the origin in the interior is also stated in §3, p. 9 ("we are assuming that the origin is in the
interior of P"). -/
def IsPolytope {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∃ V : Finset (EuclideanSpace ℝ (Fin n)), C = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))) ∧
    (0 : EuclideanSpace ℝ (Fin n)) ∈ interior C

end ConeLifts.NonnegRank
