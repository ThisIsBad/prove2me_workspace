import Mathlib
import Definitions.Def_Disjunctive_Polarity_Polars

namespace Disjunctive.Polarity

open Pointwise

/-- Theorem 2.14 (Balas §2.4, p. 32): if `0 ∉ cl conv S`, the double reverse polar `S##` equals
the Minkowski sum of the closed convex hull of `S` and the closure of its conic hull. -/
theorem reverse_polar_involution {n : ℕ} (S : Set (Fin n → ℝ))
    (h0 : 0 ∉ closure (convexHull ℝ S)) :
    ReversePolar (ReversePolar S) = closure (convexHull ℝ S) + closure (ConeHull S) := by sorry

end Disjunctive.Polarity

