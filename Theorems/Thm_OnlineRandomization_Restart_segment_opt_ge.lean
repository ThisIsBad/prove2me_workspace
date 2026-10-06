import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_GameProperties
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

namespace OnlineRandomization.Restart

/-- p. 18: for a monotone game, every segment `r(i)` except the last one, `i = 1, …, t − 1`,
has off-line optimum `c(i) = c(r(i)) ≥ H`. -/
theorem segment_opt_ge {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A)
    (hmono : IsMonotone F) (H : ℝ) (r : List R) :
    ∀ s ∈ (segments F H r).dropLast, H ≤ F.opt s := by sorry

end OnlineRandomization.Restart

