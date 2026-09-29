import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Constructions

namespace ResourceScheduling.Chain
theorem chainSchedule_of_threePartition (P : ThreePartition) (hP : P.Valid)
    (hS : P.HasSolution) :
    ∃ σ : Schedule P.chainInstance, σ.Feasible ∧ σ.cmax = ((2 * P.t * P.b : ℕ) : ℝ) := by sorry
end ResourceScheduling.Chain
