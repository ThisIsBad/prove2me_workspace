import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

/-- Theorem 1 (Rounding Theorem), p. 3: every vertex `x̃` of (LP) can be rounded to a 0-1 solution of
(IP) supported on `x̃`. -/
theorem theorem_1 {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (x : Matrix (Fin m) (Fin n) ℝ) (hx : IsLPVertex P d t x) :
    ∃ σ : Fin n → Fin m, SupportedOn x σ ∧ IPFeasible P d t σ := by sorry

end UnrelatedSched.TwoApprox

