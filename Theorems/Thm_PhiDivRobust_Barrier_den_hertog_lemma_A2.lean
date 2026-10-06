import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_IsSelfConcordant
import Definitions.Def_PhiDivRobust_Barrier_perspective
import Definitions.Def_PhiDivRobust_Barrier_logBarrier

namespace PhiDivRobust.Barrier

theorem den_hertog_lemma_A2 (f : ℝ → ℝ) (β : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioi 0) f) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (hβ : 0 ≤ β)
    (h36 : ∀ s y : ℝ, 0 < s → 0 < y → ∀ h : ℝ × ℝ,
      |iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h)| ≤
        β * iteratedFDeriv ℝ 2 (perspective f) (s, y) (fun _ => h) *
          Real.sqrt (h.1 ^ 2 / s ^ 2 + h.2 ^ 2 / y ^ 2)) :
    IsSelfConcordant (1 + β / 3) (barrierDomain f) (logBarrier f) := by sorry

end PhiDivRobust.Barrier

