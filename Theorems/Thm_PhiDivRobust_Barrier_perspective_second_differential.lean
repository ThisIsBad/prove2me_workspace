import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_perspective

namespace PhiDivRobust.Barrier

theorem perspective_second_differential (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0))
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (perspective f) (s, y) (fun _ => h) =
      iteratedDeriv 2 f (s / y) *
        (h.1 ^ 2 / y - 2 * s * h.1 * h.2 / y ^ 2 + s ^ 2 * h.2 ^ 2 / y ^ 3) := by sorry

end PhiDivRobust.Barrier
