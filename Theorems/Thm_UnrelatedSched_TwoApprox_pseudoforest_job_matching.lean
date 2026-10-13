import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

/-- §2, proof of Theorem 1, pp. 4–5: in a machine–job pseudoforest, any set of jobs each of degree
at least 2 can be matched into the machines. -/
theorem pseudoforest_job_matching {m n : ℕ} (hm : 0 < m)
    (E : Finset (Fin m × Fin n)) (hE : IsPseudoforest E)
    (T : Finset (Fin n)) (hdeg : ∀ j ∈ T, 2 ≤ (E.filter fun e => e.2 = j).card) :
    ∃ f : Fin n → Fin m, (∀ j ∈ T, (f j, j) ∈ E) ∧ Set.InjOn f (T : Set (Fin n)) := by sorry

end UnrelatedSched.TwoApprox

