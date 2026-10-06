import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_perspective

namespace PhiDivRobust.Barrier

theorem perspective_compatibility (f : ℝ → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioi 0) f) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (hκ : 0 < κ)
    (h33 : ∀ s : ℝ, 0 < s → |iteratedDeriv 3 f s| ≤ κ * iteratedDeriv 2 f s / s)
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    |iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h)| ≤
      (3 + κ * Real.sqrt 2) * iteratedFDeriv ℝ 2 (perspective f) (s, y) (fun _ => h) *
        Real.sqrt (h.1 ^ 2 / s ^ 2 + h.2 ^ 2 / y ^ 2) := by sorry

end PhiDivRobust.Barrier

