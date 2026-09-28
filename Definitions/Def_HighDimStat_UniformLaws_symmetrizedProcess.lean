import Mathlib

namespace HighDimStat.UniformLaws

/-- **Eq. (4.19)**, Wainwright, *High-Dimensional Statistics* (2019), p. 107. The symmetrized
process `‖Sₙ‖_F := sup_{f∈F} |(1/n)∑ᵢεᵢf(Xᵢ)|`, for a function class `F = {f_j, j∈ι}`, a sample
`X₁,...,Xₙ`, and an independent Rademacher sequence `ε₁,...,εₙ`. -/
noncomputable def symmetrizedProcess {D ι Ω : Type*} [MeasurableSpace D] (f : ι → D → ℝ)
    (Xs : ℕ → Ω → D) (eps : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ j : ι, |(1 / (n : ℝ)) * ∑ i ∈ Finset.range n, eps i ω * f j (Xs i ω)|

end HighDimStat.UniformLaws
