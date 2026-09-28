import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Accel_Algorithm3
import Definitions.Def_ThreeOpSplitting_Accel_Stepsizes

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.Accel

/-- Theorem 3.3 (Accelerated variants of Algorithm 1), both parts. `A`, `B` are maximal
monotone, `B` is `μ_B`-strongly monotone with `μ_B ≥ 0`, `JA`, `JB` are their resolvent
families, and `x_A^0` is the initial point of Algorithm 3.

1. If `C` is `β`-cocoercive and `μ_C`-strongly monotone, `η ∈ (0,1)`, `γ_0 ∈ (0, 2β(1-η))` and
   the stepsizes follow (3.6), then for every zero `x*` of `A + B + C` there is `K` with
   `‖x_B^k - x*‖² ≤ K/(k+1)²` for all `k`.
2. If `C` is monotone and `L_C`-Lipschitz (`L_C > 0`), `μ_B > 0`, `γ_0 ∈ (0, 2μ_B/L_C²)` and the
   stepsizes follow (3.7), the same conclusion holds. -/
theorem accelerated_rate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (JA JB : ℝ → H → H) (μB : ℝ) (xA0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hμB : 0 ≤ μB) (hBs : IsStronglyMonotoneOp μB B)
    (hJA : IsResolventFamily A JA) (hJB : IsResolventFamily B JB) :
    (∀ (C : H → H) (β μC η γ0 : ℝ),
      0 < β → IsCocoercive β C → 0 < μC → IsStronglyMonotoneFun μC C →
      0 < η → η < 1 → 0 < γ0 → γ0 < 2 * β * (1 - η) →
      ∀ xs ∈ zer (opSum A B C), ∃ K : ℝ, ∀ k : ℕ,
        ‖(accelIter JA JB C (stepsPart1 μB μC η γ0) xA0 k).xB - xs‖ ^ 2
          ≤ K / ((k : ℝ) + 1) ^ 2) ∧
    (∀ (C : H → H) (LC γ0 : ℝ),
      IsMonotoneFun C → 0 < LC → IsLipschitzOp LC C →
      0 < μB → 0 < γ0 → γ0 < 2 * μB / LC ^ 2 →
      ∀ xs ∈ zer (opSum A B C), ∃ K : ℝ, ∀ k : ℕ,
        ‖(accelIter JA JB C (stepsPart2 μB LC γ0) xA0 k).xB - xs‖ ^ 2
          ≤ K / ((k : ℝ) + 1) ^ 2) := by sorry

end ThreeOpSplitting.Accel

