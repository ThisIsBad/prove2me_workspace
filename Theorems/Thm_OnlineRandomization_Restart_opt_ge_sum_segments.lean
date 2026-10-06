import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_GameProperties

namespace OnlineRandomization.Restart

/-- p. 18: if `D` bounds the diameter, then for every decomposition of a request sequence into
`t ≥ 1` consecutive pieces `r(1), …, r(t)`,
`c(r(1) ⋯ r(t)) ≥ c(r(1)) + Σ_{i=2}^{t} (c(r(i)) − D)`. -/
theorem opt_ge_sum_segments {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (D : ℝ)
    (hD : DiameterBound F D) (segs : List (List R)) (hsegs : segs ≠ []) :
    (segs.map F.opt).sum - ((segs.length : ℝ) - 1) * D ≤ F.opt segs.flatten := by sorry

end OnlineRandomization.Restart

