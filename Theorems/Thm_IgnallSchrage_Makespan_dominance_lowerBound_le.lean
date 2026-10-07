import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound

namespace IgnallSchrage.Makespan

/-- p. 404: if `J` dominates `I` (the same jobs, `TIMEB(J) ≤ TIMEB(I)`, `TIMEC(J) ≤ TIMEC(I)`),
then `LB(J) ≤ LB(I)`; equivalently, a node cannot dominate a node with a smaller lower bound. -/
theorem dominance_lowerBound_le {n : ℕ} (a b c : Fin n → ℝ) (J I : List (Fin n))
    (hJI : J.Perm I) (hB : (times a b c J).2.1 ≤ (times a b c I).2.1)
    (hC : (times a b c J).2.2 ≤ (times a b c I).2.2) :
    lowerBound a b c J ≤ lowerBound a b c I := by sorry

end IgnallSchrage.Makespan

