import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem f_ge_max_add_mean {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n) (hD : D.IsProb)
    (j : Fin (n + 1)) (hj : j ≠ 0) :
    (N.pred j).sup' (N.pred_nonempty hj) (fun i => fNum N D i + meanLength D i j) ≤
      fNum N D j := by sorry
end FulkersonPERT.Bounds

