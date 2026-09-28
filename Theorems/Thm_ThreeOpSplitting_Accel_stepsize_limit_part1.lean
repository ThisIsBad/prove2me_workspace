import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_Stepsizes

open Filter Topology

namespace ThreeOpSplitting.Accel

/-- Proof of Theorem 3.3, Part 1 (p. 845): for the stepsizes (3.6),
`lim_{k→∞} (k + 1)γ_k = 1/(μ_Cη + μ_B)`. -/
theorem stepsize_limit_part1 (μB μC η γ0 : ℝ)
    (hμB : 0 ≤ μB) (hμC : 0 < μC) (hη0 : 0 < η) (hη1 : η < 1) (hγ0 : 0 < γ0) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) * stepsPart1 μB μC η γ0 k) atTop
      (𝓝 (1 / (μC * η + μB))) := by sorry

end ThreeOpSplitting.Accel

