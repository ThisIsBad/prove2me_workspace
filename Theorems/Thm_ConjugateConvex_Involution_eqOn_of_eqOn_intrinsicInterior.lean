import Mathlib

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §4, p. 76, the clause "as both functions are convex and semi-continuous from
below, also at the boundary points of G": two functions convex and semi-continuous from below
on a convex set `G` that agree at the (relative) interior points of `G` agree on all of `G`. -/
theorem eqOn_of_eqOn_intrinsicInterior {n : ℕ} (G : Set (Fin n → ℝ)) (f g : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ G f) (hg : ConvexOn ℝ G g)
    (hfl : LowerSemicontinuousOn f G) (hgl : LowerSemicontinuousOn g G)
    (hfg : Set.EqOn f g (intrinsicInterior ℝ G)) :
    Set.EqOn f g G := by sorry

end ConjugateConvex.Involution

