import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem expected_critical_path_bounds {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n)
    (hD : D.IsProb) :
    ∀ i : Fin (n + 1), meanCPL N D i ≤ fNum N D i ∧ fNum N D i ≤ expectedLength N D i := by sorry
end FulkersonPERT.Bounds

