import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupportVectorMachines.Concentration

/-- Theorem 6.12 (Bernstein's inequality), p. 213: let `(Ω, A, P)` be a probability space,
`B > 0` and `σ > 0` be real numbers, and `n ≥ 1` be an integer. Let `ξ₁,…,ξₙ : Ω → ℝ` be
independent random variables satisfying `E ξᵢ = 0`, `‖ξᵢ‖_∞ ≤ B`, and `E ξᵢ² ≤ σ²` for all
`i = 1,…,n`. Then, for all `τ > 0`,
`P((1/n) ∑ᵢ ξᵢ ≥ √(2σ²τ/n) + 2Bτ/(3n)) ≤ e^{-τ}`. -/
theorem theorem_6_12_bernstein_scalar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B σ : ℝ) (hB : 0 < B) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (ξ : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (hbound : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ B)
    (hvar : ∀ i, ∫ ω, (ξ i ω) ^ 2 ∂P ≤ σ ^ 2) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | Real.sqrt (2 * σ ^ 2 * τ / n) + 2 * B * τ / (3 * n) ≤
        (1 / (n : ℝ)) * ∑ i, ξ i ω} ≤ Real.exp (-τ) := by sorry

end SupportVectorMachines.Concentration

