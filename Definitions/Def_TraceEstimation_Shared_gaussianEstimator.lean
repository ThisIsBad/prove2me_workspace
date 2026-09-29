import Mathlib

namespace TraceEstimation.Shared

open MeasureTheory ProbabilityTheory Matrix

/-- The sample space of the Gaussian trace estimator with `M` samples in dimension `n`:
`M` random vectors `z_1, …, z_M ∈ ℝⁿ` whose `M·n` entries are i.i.d. standard normal
(Avron–Toledo, Definition 3.1, p. 8:3). It is the product of `M · n` copies of `N(0,1)`. -/
noncomputable def gaussianSampleMeasure (n M : ℕ) : Measure (Fin M → Fin n → ℝ) :=
  Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin n => gaussianReal 0 1

/-- The Gaussian trace estimator `G_M = (1/M) ∑_{i=1}^M z_iᵀ A z_i` of Definition 3.1
(Avron–Toledo, p. 8:3), as a function of the sample `ω = (z_1, …, z_M)`. -/
noncomputable def gaussianEstimator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (M : ℕ)
    (ω : Fin M → Fin n → ℝ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i : Fin M, ω i ⬝ᵥ (A *ᵥ ω i)

end TraceEstimation.Shared
