import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem sum_max_add_le_expectedLength {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n)
    (hD : D.IsProb) (j : Fin (n + 1)) (hj : j ≠ 0) :
    ∑ v ∈ D.supp j, D.p j v *
        (N.pred j).sup' (N.pred_nonempty hj) (fun i => expectedLength N D i + v i) ≤
      expectedLength N D j := by sorry
end FulkersonPERT.Bounds

