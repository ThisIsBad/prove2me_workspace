import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupportVectorMachines.Concentration

/-- Corollary 6.15 (Hoeffding's inequality in Hilbert spaces), p. 217: let `(Ω, A, P)` be a
probability space, `H` be a separable Hilbert space, and `B > 0`. Let `ξ₁,…,ξₙ : Ω → H` be
independent `H`-valued random variables satisfying `‖ξᵢ‖_∞ ≤ B` for all `i = 1,…,n`. Then, for
all `τ > 0`,
`P(‖(1/n) ∑ᵢ (ξᵢ - E ξᵢ)‖_H ≥ B√(2τ/n) + B√(1/n) + 4Bτ/(3n)) ≤ e^{-τ}`. -/
theorem corollary_6_15_hoeffding_hilbert_space {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 0 < n) (ξ : Fin n → Ω → H)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hbound : ∀ i, ∀ᵐ ω ∂P, ‖ξ i ω‖ ≤ B) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | B * Real.sqrt (2 * τ / n) + B * Real.sqrt (1 / n) + 4 * B * τ / (3 * n) ≤
        ‖(1 / (n : ℝ)) • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖} ≤ Real.exp (-τ) := by sorry

end SupportVectorMachines.Concentration

