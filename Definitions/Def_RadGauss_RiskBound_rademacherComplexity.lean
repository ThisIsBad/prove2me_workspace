import Mathlib

open MeasureTheory
open scoped ENNReal

namespace RadGauss.RiskBound

/-- The ±1 value encoded by a Boolean sign: `true ↦ 1`, `false ↦ -1`. -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

/-- **Definition 2** (p. 464), the empirical Rademacher complexity
`R̂_n(G) = E[ sup_{g ∈ G} |(2/n) Σ_{i=1}^n σ_i g(x_i)| | x_1, …, x_n ]` of a class `G` of real
functions at the sample `x = (x_1, …, x_n)`. The expectation over independent uniform signs
`σ_1, …, σ_n ∈ {±1}` is the average over all `2^n` sign vectors `σ : Fin n → Bool`
(encoded by `signVal`). Values are in `ℝ≥0∞`, so an unbounded class has complexity `⊤`
and the empty class has complexity `0`. -/
noncomputable def empiricalRademacher {Z : Type*} (n : ℕ) (G : Set (Z → ℝ))
    (x : Fin n → Z) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ n)⁻¹ *
    ∑ σ : Fin n → Bool, ⨆ g ∈ G, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, signVal (σ i) * g (x i)|

/-- **Definition 2** (p. 464), the Rademacher complexity `R_n(G) = E R̂_n(G)`: the expectation
of the empirical Rademacher complexity over an i.i.d. sample `x_1, …, x_n` drawn from the
probability measure `μ`, as a lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def rademacherComplexity {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (n : ℕ) (G : Set (Z → ℝ)) : ℝ≥0∞ :=
  ∫⁻ x, empiricalRademacher n G x ∂(Measure.pi fun _ : Fin n => μ)

end RadGauss.RiskBound
