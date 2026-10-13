import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_FixedMachines_LongAssignment
import Definitions.Def_UnrelatedSched_FixedMachines_BinarySearch

namespace UnrelatedSched.FixedMachines

open MatousekLP.Scheduling

/-- Theorem 3 (p. 6), as its proof establishes it: for every number `m ≥ 1` of machines, every
positive integer processing-time matrix `P`, every `ε > 0` and every LP solver `V`, the
procedure `A_ε` run with `V` exists, and the binary search of Lemma 1 driven by any such
procedure outputs a schedule whose makespan is at most `(1 + ε)` times the optimal makespan. -/
theorem theorem_3 {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε)
    (V : ℕ → (Fin n → Option (Fin m)) → Option (Matrix (Fin m) (Fin n) ℝ))
    (hV : IsVertexSelector P ε V) (σopt : Fin n → Fin m)
    (hopt : IsOptimalSchedule (fun i j => (P i j : ℝ)) σopt) :
    (∃ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D) ∧
    ∀ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D →
      makespan (fun i j => (P i j : ℝ)) (binarySearch hm P D) ≤
        (1 + ε) * makespan (fun i j => (P i j : ℝ)) σopt := by sorry

end UnrelatedSched.FixedMachines

