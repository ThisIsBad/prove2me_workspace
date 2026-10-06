import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_perspective

namespace PhiDivRobust.Barrier

theorem perspective_third_differential (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0))
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h) =
      iteratedDeriv 2 f (s / y) *
          (-(3 * h.1 ^ 2 * h.2 / y ^ 2) + 6 * s * h.1 * h.2 ^ 2 / y ^ 3
            - 3 * s ^ 2 * h.2 ^ 3 / y ^ 4)
        + iteratedDeriv 3 f (s / y) *
          (h.1 ^ 3 / y ^ 2 - 3 * s * h.1 ^ 2 * h.2 / y ^ 3 + 3 * s ^ 2 * h.1 * h.2 ^ 2 / y ^ 4
            - s ^ 3 * h.2 ^ 3 / y ^ 5) := by sorry

end PhiDivRobust.Barrier

