import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_Stepsizes

open Filter Topology

namespace ThreeOpSplitting.Accel

/-- Proof of Theorem 3.3, Part 2 (p. 846): for the stepsizes (3.7),
`lim_{k→∞} (k + 1)γ_k = 1/μ_B`. -/
theorem stepsize_limit_part2 (μB LC γ0 : ℝ)
    (hμB : 0 < μB) (hLC : 0 < LC) (hγ0 : 0 < γ0) (hγ0' : γ0 < 2 * μB / LC ^ 2) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) * stepsPart2 μB LC γ0 k) atTop (𝓝 (1 / μB)) := by sorry

end ThreeOpSplitting.Accel

