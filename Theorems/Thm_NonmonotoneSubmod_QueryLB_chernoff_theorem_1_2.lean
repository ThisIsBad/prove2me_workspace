import Mathlib

open MeasureTheory ProbabilityTheory

namespace NonmonotoneSubmod.QueryLB

/-- Theorem 1.2 (Feige–Mirrokni–Vondrák 2011, p. 1137, quoted from Alon–Spencer): if
`Y₁, …, Y_t` are independent random variables with values in `[−1, 1]` and `E[Yᵢ] = 0`, then
`Pr[∑ Yᵢ > λ] ≤ e^{−λ²/2t}` for every `λ > 0`. -/
theorem chernoff_theorem_1_2 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : ℕ) (Y : Fin t → Ω → ℝ) (hmeas : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (hbd : ∀ i ω, Y i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0) (lam : ℝ) (hlam : 0 < lam) :
    μ.real {ω | lam < ∑ i, Y i ω} ≤ Real.exp (-(lam ^ 2 / (2 * t))) := by sorry

end NonmonotoneSubmod.QueryLB
