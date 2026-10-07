import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem earliest_isGreatest_pathLength {n : ℕ} (N : ProjectNetwork n)
    (y : Fin (n + 1) → Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    IsGreatest {L : ℝ | ∃ p : List (Fin (n + 1)), IsPathTo N p i ∧ L = pathLength y p}
      (earliest N y i) := by sorry
end FulkersonPERT.Bounds

