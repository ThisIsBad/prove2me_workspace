import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RadGauss.LipschitzGaussian

/-- **Definition 2** (p. 464), the empirical Gaussian complexity
`Ĝ_n(F) = E[ sup_{f ∈ F} |(2/n) Σ_{i=1}^n g_i f(x_i)| | x_1, …, x_n ]` of a class `F` of real
functions at the sample `x = (x_1, …, x_n)`, where `g_1, …, g_n` are independent standard
Gaussian `N(0,1)` variables. The Gaussian vector is the coordinate vector of the product measure
`N(0,1)^{⊗n}` on `Fin n → ℝ`, and the expectation is a lower Lebesgue integral in `ℝ≥0∞`, so an
unbounded class has complexity `⊤` and the empty class has complexity `0`. -/
noncomputable def empiricalGaussian {Z : Type*} (n : ℕ) (F : Set (Z → ℝ)) (x : Fin n → Z) :
    ℝ≥0∞ :=
  ∫⁻ g : Fin n → ℝ, ⨆ f ∈ F, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, g i * f (x i)|
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)

/-- **Definition 2** (p. 464), the Gaussian complexity `G_n(F) = E Ĝ_n(F)`: the expectation of
the empirical Gaussian complexity over an i.i.d. sample `X_1, …, X_n` drawn from the
probability measure `μ` (the product measure `μ^{⊗n}`), as a lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def gaussianComplexity {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (n : ℕ)
    (F : Set (Z → ℝ)) : ℝ≥0∞ :=
  ∫⁻ x, empiricalGaussian n F x ∂(Measure.pi fun _ : Fin n => μ)

end RadGauss.LipschitzGaussian
