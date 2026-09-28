import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupportVectorMachines.Concentration

/-- Theorem 6.13, p. 214: let `(Ω, A, P)` be a probability space, `E` be a separable Banach
space, and `ξ₁,…,ξₙ : Ω → E` be independent, `E`-valued, `P`-integrable random variables. Then,
for all `ε > 0` and all `t ≥ 0`,
`P(‖∑ᵢ ξᵢ‖ ≥ εn) ≤ exp(-tεn + t·E‖∑ᵢ ξᵢ‖ + ∑ᵢ E(e^{t‖ξᵢ‖} - 1 - t‖ξᵢ‖))`. -/
theorem theorem_6_13_banach_space_concentration {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E]
    (n : ℕ)
    (ξ : Fin n → Ω → E) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hint : ∀ i, Integrable (ξ i) P) (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | ε * n ≤ ‖∑ i, ξ i ω‖} ≤
      Real.exp (-t * ε * n + t * (∫ ω, ‖∑ i, ξ i ω‖ ∂P) +
        ∑ i, ∫ ω, (Real.exp (t * ‖ξ i ω‖) - 1 - t * ‖ξ i ω‖) ∂P) := by sorry

end SupportVectorMachines.Concentration

