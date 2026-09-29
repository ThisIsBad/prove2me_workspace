import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §1, p. 2: no set is both approachable and excludable. -/
theorem not_approachable_and_excludable {N r s : ℕ} (G : Game N r s) (hr : 1 ≤ r)
    (hs : 1 ≤ s) (S : Set (E N)) : ¬ (G.ApproachableIn S ∧ G.ExcludableIn S) := by sorry

end VectorPayoffs.Convex
