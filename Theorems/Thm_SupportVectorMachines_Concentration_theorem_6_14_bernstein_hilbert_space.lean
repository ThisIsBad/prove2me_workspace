import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupportVectorMachines.Concentration

/-- Theorem 6.14 (Bernstein's inequality in Hilbert spaces), p. 216: let `(Ω, A, P)` be a
probability space, `H` be a separable Hilbert space, `B > 0`, and `σ > 0`. Let
`ξ₁,…,ξₙ : Ω → H` be independent random variables satisfying `E ξᵢ = 0`, `‖ξᵢ‖_∞ ≤ B`, and
`E ‖ξᵢ‖²_H ≤ σ²` for all `i = 1,…,n`. Then, for all `τ > 0`,
`P(‖(1/n) ∑ᵢ ξᵢ‖_H ≥ √(2σ²τ/n) + √(σ²/n) + 2Bτ/(3n)) ≤ e^{-τ}`. -/
theorem theorem_6_14_bernstein_hilbert_space {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
    (B σ : ℝ) (hB : 0 < B) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n) (ξ : Fin n → Ω → H)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (hbound : ∀ i, ∀ᵐ ω ∂P, ‖ξ i ω‖ ≤ B)
    (hvar : ∀ i, ∫ ω, ‖ξ i ω‖ ^ 2 ∂P ≤ σ ^ 2) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | Real.sqrt (2 * σ ^ 2 * τ / n) + Real.sqrt (σ ^ 2 / n) + 2 * B * τ / (3 * n) ≤
        ‖(1 / (n : ℝ)) • ∑ i, ξ i ω‖} ≤ Real.exp (-τ) := by sorry

end SupportVectorMachines.Concentration

