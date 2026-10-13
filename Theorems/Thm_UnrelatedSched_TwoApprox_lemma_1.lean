import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP
import Definitions.Def_UnrelatedSched_TwoApprox_Algorithm

namespace UnrelatedSched.TwoApprox

open MatousekLP.Scheduling

/-- Lemma 1, p. 5: the binary search driven by a `ρ`-relaxed decision procedure outputs a schedule
of makespan at most `ρ` times the optimum. -/
theorem lemma_1 {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) (hP : ∀ i j, 0 < P i j)
    (ρ : ℝ) (D : DecisionProcedure m n) (hD : IsRelaxedDecisionProcedure P ρ D)
    (σopt : Fin n → Fin m) (hopt : IsOptimalSchedule (realTimes P) σopt) :
    makespan (realTimes P) (binarySearch P hm D) ≤ ρ * makespan (realTimes P) σopt := by sorry

end UnrelatedSched.TwoApprox

