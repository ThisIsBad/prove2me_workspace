import Mathlib

open MeasureTheory

namespace HighDimStat.UniformLaws

/-- **Eq. (4.7)**, Wainwright, *High-Dimensional Statistics* (2019), p. 100. The empirical
process deviation `‖Pₙ-P‖_F := sup_{f∈F} |(1/n)∑ᵢf(Xᵢ) - E[f(X)]|`, for a function class
`F = {f_j, j∈ι}`, a sample `X₁,...,Xₙ`, and a population variable `X₀` with the shared law. -/
noncomputable def empProcessDeviation {D ι Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (f : ι → D → ℝ)
    (Xs : ℕ → Ω → D) (X0 : Ω → D) (Prob : Measure Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ j : ι, |(1 / (n : ℝ)) * ∑ i ∈ Finset.range n, f j (Xs i ω) - ∫ ω', f j (X0 ω') ∂Prob|

end HighDimStat.UniformLaws
