import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP
import Definitions.Def_UnrelatedSched_TwoApprox_Algorithm

namespace UnrelatedSched.TwoApprox

/-- §3, pp. 5–6: the LP rounding procedure is a 2-relaxed decision procedure. -/
theorem lp_procedure_two_relaxed {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (hV : IsVertexSelector P V)
    (D : DecisionProcedure m n) (hD : IsLPRoundingProcedure P V D) :
    IsRelaxedDecisionProcedure P 2 D := by sorry

end UnrelatedSched.TwoApprox

