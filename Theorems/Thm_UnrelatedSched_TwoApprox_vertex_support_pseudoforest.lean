import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

/-- §2, proof of Theorem 1, p. 4: the support graph of a vertex of (LP) is a pseudoforest. -/
theorem vertex_support_pseudoforest {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ)
    (t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ) (hx : IsLPVertex P d t x) :
    IsPseudoforest (supportEdges x) := by sorry

end UnrelatedSched.TwoApprox

