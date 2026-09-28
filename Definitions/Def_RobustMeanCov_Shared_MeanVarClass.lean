import Mathlib
open MeasureTheory

namespace RobustMeanCov.Shared

/-- The univariate class `𝕄_(m,v)` (Popescu 2007, p. 100, "with the default superscript
`n = 1`"): probability measures `ν` on `ℝ` with finite second moment, mean `m` and variance `v`.
The second parameter is the variance `v = σ²`, as in the paper's subscript `(μ_x, σ_x²)`. -/
def MeanVarClass (m v : ℝ) : Set (Measure ℝ) :=
  {ν | IsProbabilityMeasure ν ∧ MemLp (fun r : ℝ => r) 2 ν ∧
    ∫ r, r ∂ν = m ∧ ∫ r, (r - m) ^ 2 ∂ν = v}

end RobustMeanCov.Shared
