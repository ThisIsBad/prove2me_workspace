import Mathlib

namespace ConeLifts.Factorization

/-- A **convex body** in `ℝⁿ` in the sense of Gouveia, Parrilo & Thomas, *Lifts of Convex Sets and
Cone Factorizations*, arXiv:1111.3164v2, §2, p. 3: a convex set that is compact and contains the
origin in its interior. The paper assumes "throughout" that every convex set whose lifts it studies
is a convex body. `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`.

Not Mathlib's `ConvexBody` (compact, convex, nonempty): here the origin must be an interior point. -/
def IsConvexBody {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsCompact C ∧ Convex ℝ C ∧ (0 : EuclideanSpace ℝ (Fin n)) ∈ interior C

end ConeLifts.Factorization
