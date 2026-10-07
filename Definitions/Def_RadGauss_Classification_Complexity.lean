import Mathlib

open MeasureTheory

namespace RadGauss.Classification

/-- **Empirical Rademacher complexity** (Bartlett–Mendelson 2002, Definition 2, p. 464):
`R̂_n(F)(x) = E_σ [ sup_{f ∈ F} |(2/n) Σ_{i} σ_i f(x_i)| ]` for a sample `x = (x_1, …, x_n)`,
where `σ_1, …, σ_n` are independent uniform `{±1}`-valued random variables.
The expectation over `σ` is the exact average over all `2^n` sign vectors `σ : Fin n → ℤˣ`
(`ℤˣ = {1, -1}`, coerced to `ℝ`). The value lies in `ℝ≥0∞`, so an unbounded class has
complexity `⊤`, and the supremum over the empty class is `0`. -/
noncomputable def empiricalRademacher {X : Type*} (F : Set (X → ℝ)) (n : ℕ) (x : Fin n → X) :
    ENNReal :=
  (2 ^ n : ENNReal)⁻¹ * ∑ σ : Fin n → ℤˣ,
    ⨆ f ∈ F, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, ((σ i : ℤ) : ℝ) * f (x i)|

/-- **Rademacher complexity** (Definition 2, p. 464): `R_n(F) = E R̂_n(F)`, the expectation of
the empirical Rademacher complexity over an i.i.d. sample `X_1, …, X_n ∼ μ`
(the product measure `μ^n`), as a lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def rademacherComplexity {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (n : ℕ) (F : Set (X → ℝ)) : ENNReal :=
  ∫⁻ x, empiricalRademacher F n x ∂(Measure.pi fun _ : Fin n => μ)

end RadGauss.Classification
