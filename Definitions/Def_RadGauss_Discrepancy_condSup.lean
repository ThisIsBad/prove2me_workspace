import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

open MeasureTheory

namespace RadGauss.Discrepancy

/-- The integer sum `Σ_{i=1}^n σ_i` of a sign vector (`true ↦ 1`, `false ↦ -1`, as in
`signVal`). -/
def sumSign {n : ℕ} (σ : Fin n → Bool) : ℤ := ∑ i, if σ i then (1 : ℤ) else -1

/-- The function `s` of Appendix A (p. 478):
`s(N) = (2/n) E[ sup_{f ∈ F} Σ_{i=1}^n σ_i f(X_i) | Σ_{i=1}^n σ_i = N ]`,
where `X_1, …, X_n` are i.i.d. from `μ` and `σ_1, …, σ_n` are independent uniform signs,
independent of the sample. Conditioning on `Σ σ_i = N` makes `σ` uniform on the sign vectors with
that sum, so `s(N)` is the average, over those sign vectors, of
`(2/n) ∫ sup_{f ∈ F} Σ σ_i f(x_i) dμⁿ(x)`. No absolute value. The supremum is a real supremum
over the subtype `F`; the value is meaningful for `N` attained by some sign vector (otherwise the
average is over the empty set and equals `0`). -/
noncomputable def condSup {X : Type*} [MeasurableSpace X] (μ : Measure X) (n : ℕ)
    (F : Set (X → ℝ)) (N : ℤ) : ℝ :=
  (2 / (n : ℝ)) *
    (((Finset.univ.filter fun σ : Fin n → Bool => sumSign σ = N).card : ℝ)⁻¹ *
      ∑ σ ∈ Finset.univ.filter (fun σ : Fin n → Bool => sumSign σ = N),
        ∫ x, (⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) ∂(Measure.pi fun _ : Fin n => μ))

end RadGauss.Discrepancy
