import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Accel_Algorithm3
import Definitions.Def_ThreeOpSplitting_Accel_Stepsizes

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.Accel

/-- Proposition 3.1, Part 1 (inequality (3.9)), for every iteration `k ≥ 1` of recursion (3.8).
The paper writes "for all `k ≥ 0`"; at `k = 0` the point `x_A^0` is the free initial point, not a
resolvent output, and (3.9) fails in general. -/
theorem prop_3_1_part1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (JA JB : ℝ → H → H)
    (μB μC β η : ℝ) (γ : ℕ → ℝ) (xA0 xs uAs uBs : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hμB : 0 ≤ μB) (hBs : IsStronglyMonotoneOp μB B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hμC : 0 < μC) (hCs : IsStronglyMonotoneFun μC C)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hγ : ∀ j : ℕ, 0 < γ j ∧ γ j < 2 * (1 - η) * β)
    (hJA : IsResolventFamily A JA) (hJB : IsResolventFamily B JB)
    (huA : uAs ∈ A xs) (huB : uBs ∈ B xs) (hsum : uAs + uBs + C xs = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (1 + 2 * γ k * μB) * ‖(accelIter JA JB C γ xA0 (k + 1)).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 (k + 1)).uB - uBs‖ ^ 2
        + (1 - γ k / (2 * (1 - η) * β))
          * ‖(accelIter JA JB C γ xA0 k).xA - (accelIter JA JB C γ xA0 k).xB‖ ^ 2
      ≤ (1 - 2 * γ k * μC * η) * ‖(accelIter JA JB C γ xA0 k).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 k).uB - uBs‖ ^ 2 := by sorry

end ThreeOpSplitting.Accel

