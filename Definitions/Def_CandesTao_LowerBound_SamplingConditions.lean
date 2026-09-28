import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CandesTao.LowerBound

/-- Condition (I.20) of Candès–Tao Theorem 1.7 for `n × n` matrices, `m` samples,
rank bound `r`, incoherence parameter `μ₀` and failure level `δ`:
`m ≥ n² (1 - exp(-(μ₀ r / n) log(n / (2δ))))`, with the natural logarithm. -/
def SamplingConditionI20 (n m r : ℕ) (μ₀ δ : ℝ) : Prop :=
  (m : ℝ) ≥ (n : ℝ) ^ 2 * (1 - Real.exp (-(μ₀ * r / n) * Real.log (n / (2 * δ))))

/-- The quantity `ε := ½ (μ₀ r / n) log(n / (2δ))` of Candès–Tao Theorem 1.7. -/
noncomputable def epsilonI21 (n r : ℕ) (μ₀ δ : ℝ) : ℝ :=
  (1 / 2) * (μ₀ * r / n) * Real.log (n / (2 * δ))

/-- Condition (I.21) of Candès–Tao Theorem 1.7:
`m ≥ (1 - ε) μ₀ n r log(n / (2δ))` with `ε = epsilonI21 n r μ₀ δ`. -/
def SamplingConditionI21 (n m r : ℕ) (μ₀ δ : ℝ) : Prop :=
  (m : ℝ) ≥ (1 - epsilonI21 n r μ₀ δ) * μ₀ * n * r * Real.log (n / (2 * δ))

end CandesTao.LowerBound
