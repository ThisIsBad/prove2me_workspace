import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

open MatousekLP.Scheduling

/-- §3, p. 5: the 0-1 matrix of a schedule with makespan at most `d` is feasible for (LP) with
`d_1 = ⋯ = d_m = t = d`. -/
theorem yes_instance_lp_feasible {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : ℝ)
    (σ : Fin n → Fin m) (hσ : makespan (realTimes P) σ ≤ d) :
    assignmentMatrix σ ∈ LPPolytope P (fun _ => d) d := by sorry

end UnrelatedSched.TwoApprox

