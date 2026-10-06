import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_IsSelfConcordant
import Definitions.Def_PhiDivRobust_Barrier_perspective
import Definitions.Def_PhiDivRobust_Barrier_logBarrier

namespace PhiDivRobust.Barrier

theorem perspective_barrier_self_concordant (f : ℝ → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioi 0) f) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (hκ : 0 < κ)
    (h33 : ∀ s : ℝ, 0 < s → |iteratedDeriv 3 f s| ≤ κ * iteratedDeriv 2 f s / s) :
    IsSelfConcordant (2 + Real.sqrt 2 / 3 * κ) (barrierDomain f) (logBarrier f) := by sorry

end PhiDivRobust.Barrier

