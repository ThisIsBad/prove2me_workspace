import Mathlib

namespace ThreeOpSplitting.Accel

/-- The stepsize rule (3.6) of Theorem 3.3, Part 1: `γ_0 = γ0` and, for `k ≥ 0`,
`γ_{k+1} = (-2γ_k²μ_Cη + √((2γ_k²μ_Cη)² + 4(1 + 2γ_kμ_B)γ_k²)) / (2(1 + 2γ_kμ_B))`. -/
noncomputable def stepsPart1 (μB μC η γ0 : ℝ) : ℕ → ℝ
  | 0 => γ0
  | k + 1 =>
    let g := stepsPart1 μB μC η γ0 k
    (-2 * g ^ 2 * μC * η + Real.sqrt ((2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2))
      / (2 * (1 + 2 * g * μB))

/-- The stepsize rule (3.7) of Theorem 3.3, Part 2: `γ_0 = γ0` and, for `k ≥ 0`,
`γ_{k+1} = γ_k / √(1 + 2γ_k(μ_B - γ_k L_C²/2))`. -/
noncomputable def stepsPart2 (μB LC γ0 : ℝ) : ℕ → ℝ
  | 0 => γ0
  | k + 1 =>
    let g := stepsPart2 μB LC γ0 k
    g / Real.sqrt (1 + 2 * g * (μB - g * LC ^ 2 / 2))

end ThreeOpSplitting.Accel
