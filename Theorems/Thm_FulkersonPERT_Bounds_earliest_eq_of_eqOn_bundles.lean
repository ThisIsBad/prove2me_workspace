import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem earliest_eq_of_eqOn_bundles {n : ℕ} (N : ProjectNetwork n)
    (y y' : Fin (n + 1) → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (h : ∀ a b, (a, b) ∈ N.P → b ≤ i → y a b = y' a b) :
    earliest N y i = earliest N y' i := by sorry
end FulkersonPERT.Bounds

