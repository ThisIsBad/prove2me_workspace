import Mathlib
import Definitions.Def_Disjunctive_Polarity_Polars

namespace Disjunctive.Polarity

/-- Corollary 2.15 (Balas §2.4, p. 33): for any `S` with `0 ∉ cl conv S`, the closed convex hull
of `S` equals the intersection of its ordinary double polar and its reverse double polar. -/
theorem hull_eq_polar_inter_reverse_polar {n : ℕ} (S : Set (Fin n → ℝ))
    (h0 : 0 ∉ closure (convexHull ℝ S)) :
    closure (convexHull ℝ S) = Polar (Polar S) ∩ ReversePolar (ReversePolar S) := by sorry

end Disjunctive.Polarity

