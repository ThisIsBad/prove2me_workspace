import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Accel_Algorithm3
import Definitions.Def_ThreeOpSplitting_Accel_Stepsizes

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.Accel

/-- Proposition 3.1, Part 2 (inequality (3.10)), for every iteration `k ≥ 1` of recursion (3.8)
with arbitrary positive stepsizes. The paper writes "for all `k ≥ 0`"; at `k = 0` the point
`x_A^0` is the free initial point, not a resolvent output, and (3.10) fails in general. -/
theorem prop_3_1_part2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (JA JB : ℝ → H → H)
    (μB LC : ℝ) (γ : ℕ → ℝ) (xA0 xs uAs uBs : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hμB : 0 < μB) (hBs : IsStronglyMonotoneOp μB B)
    (hCm : IsMonotoneFun C) (hLC : 0 ≤ LC) (hCL : IsLipschitzOp LC C)
    (hγ : ∀ j : ℕ, 0 < γ j)
    (hJA : IsResolventFamily A JA) (hJB : IsResolventFamily B JB)
    (huA : uAs ∈ A xs) (huB : uBs ∈ B xs) (hsum : uAs + uBs + C xs = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (1 + 2 * γ k * (μB - γ k * LC ^ 2 / 2)) * ‖(accelIter JA JB C γ xA0 (k + 1)).xB - xs‖ ^ 2
        + γ k ^ 2 * LC ^ 2 * ‖(accelIter JA JB C γ xA0 (k + 1)).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 (k + 1)).uB - uBs‖ ^ 2
      ≤ ‖(accelIter JA JB C γ xA0 k).xB - xs‖ ^ 2
        + γ k ^ 2 * LC ^ 2 * ‖(accelIter JA JB C γ xA0 k).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 k).uB - uBs‖ ^ 2 := by sorry

end ThreeOpSplitting.Accel

