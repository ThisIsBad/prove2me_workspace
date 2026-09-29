import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §1, p. 2: if a closed set `S` is approachable in the transpose `M'` with a
strategy `f`, then every closed set `T` not intersecting `S` is excludable in `M` with `f`. -/
theorem transpose_excludable {N r s : ℕ} (G : Game N r s) (S T : Set (E N))
    (hS : IsClosed S) (hT : IsClosed T) (hST : Disjoint S T) (f : Strategy N s)
    (hf : G.transpose.ApproachableWith S f) : G.ExcludableWith T f := by sorry

end VectorPayoffs.Convex
