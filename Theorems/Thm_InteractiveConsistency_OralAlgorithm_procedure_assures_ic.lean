import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Procedure

namespace InteractiveConsistency.OralAlgorithm

theorem procedure_assures_ic {α V : Type*} [DecidableEq α] (P : Finset α) (m : ℕ)
    (hn : 3 * m + 1 ≤ P.card) :
    AssuresICLevel (V := V) P m (fun _ => record m P) := by sorry

end InteractiveConsistency.OralAlgorithm

