import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP
import Definitions.Def_UnrelatedSched_TwoApprox_Algorithm

namespace UnrelatedSched.TwoApprox

open MatousekLP.Scheduling

/-- Theorem 2, p. 6: for every vertex selector, the LP rounding procedure exists, and the binary
search of Lemma 1 driven by any such procedure outputs a schedule of makespan at most twice the
optimum. -/
theorem theorem_2 {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) (hP : ∀ i j, 0 < P i j)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (hV : IsVertexSelector P V)
    (σopt : Fin n → Fin m) (hopt : IsOptimalSchedule (realTimes P) σopt) :
    (∃ D : DecisionProcedure m n, IsLPRoundingProcedure P V D) ∧
      ∀ D : DecisionProcedure m n, IsLPRoundingProcedure P V D →
        makespan (realTimes P) (binarySearch P hm D) ≤ 2 * makespan (realTimes P) σopt := by sorry

end UnrelatedSched.TwoApprox

