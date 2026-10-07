import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem fNum_le_expectedLength_step {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n)
    (hD : D.IsProb) (j : Fin (n + 1))
    (ih : ∀ k : Fin (n + 1), k < j → fNum N D k ≤ expectedLength N D k) :
    fNum N D j ≤ expectedLength N D j := by sorry
end FulkersonPERT.Bounds

