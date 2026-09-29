import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §3, proof of THEOREM 3, p. 6, first paragraph: a closed convex `S` meeting
every `T(q)` satisfies the hypothesis of THEOREM 1 at every point `x ∉ S`. -/
theorem convex_blackwell_condition {N r s : ℕ} (G : Game N r s) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (S : Set (E N)) (hS : IsClosed S) (hSc : Convex ℝ S)
    (hT : ∀ q ∈ stdSimplex ℝ (Fin s), (S ∩ G.T q).Nonempty) :
    ∀ x ∉ S, ∃ p ∈ stdSimplex ℝ (Fin r), G.BlackwellCondition S p x := by sorry

end VectorPayoffs.Convex
