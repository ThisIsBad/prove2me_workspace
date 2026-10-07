import Mathlib
import Definitions.Def_RadGauss_Classification_Complexity
import Definitions.Def_RadGauss_LipschitzGaussian_GaussianComplexity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RadGauss.Kernel

/-- **Empirical Gaussian complexity** (Definition 2, p. 464):
`Ĝ_n(F)(x) = E[ sup_{f ∈ F} |(2/n) Σ_{i=1}^n g_i f(x_i)| | x_1, …, x_n ]`, where
`g_1, …, g_n` are independent standard Gaussian `N(0,1)` variables. The Gaussian vector is the
coordinate vector of the product measure `N(0,1)^{⊗n}` on `Fin n → ℝ`, and the expectation is a
lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def empiricalGaussian {X : Type*} (F : Set (X → ℝ)) (n : ℕ) (x : Fin n → X) :
    ℝ≥0∞ :=
  ∫⁻ g : Fin n → ℝ, ⨆ f ∈ F, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, g i * f (x i)|
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)

end RadGauss.Kernel
