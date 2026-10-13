import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection

namespace Disjunctive.Polarity

/-- Theorem 2.5 (Balas §2.2, p. 27): the projection of `Q` onto the `x`-space is cut out by the
inequalities `(vB)x ≤ vb` for `v` ranging over the extreme rays of the projection cone `W`. -/
theorem projection_extreme_rays {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) :
    ProjOntoX (Poly2 A B b) =
      {x : Fin q → ℝ | ∀ v, IsExtremeRay (ProjectionCone A) v →
        dotProduct (Matrix.vecMul v B) x ≤ dotProduct v b} := by sorry

end Disjunctive.Polarity

