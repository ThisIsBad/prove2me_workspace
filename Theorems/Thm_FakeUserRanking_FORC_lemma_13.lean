import Mathlib

open MeasureTheory ProbabilityTheory

namespace FakeUserRanking.FORC

/-- Lemma 13, p. 56: Hoeffding's inequality for the cross-learned weighted mean
`(1/η̂)(∑_{i ≤ η₁} X_i + ∑_{i ≤ η₂} Y_i / 2^ℓ)` with `η̂ = η₁ + η₂/2^ℓ`. -/
theorem lemma_13 {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (T : ℕ) (X Y : Fin T → Ω → ℝ) (μ : ℝ)
    (hindep : iIndepFun (Sum.elim X Y) ν)
    (hXmeas : ∀ i, Measurable (X i)) (hYmeas : ∀ i, Measurable (Y i))
    (hX01 : ∀ i, ∀ᵐ ω ∂ν, X i ω = 0 ∨ X i ω = 1)
    (hY01 : ∀ i, ∀ᵐ ω ∂ν, Y i ω = 0 ∨ Y i ω = 1)
    (hXmean : ∀ i, ∫ ω, X i ω ∂ν = μ) (hYmean : ∀ i, ∫ ω, Y i ω ∂ν = μ)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (η₁ η₂ : ℕ) (h₁ : η₁ ≤ T) (h₂ : η₂ ≤ T)
    (hη : 0 < (η₁ : ℝ) + η₂ / 2 ^ ℓ) (ε : ℝ) (hε : 0 < ε) :
    ν.real {ω | ε < |(1 / ((η₁ : ℝ) + η₂ / 2 ^ ℓ)) *
        (∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₁), X i ω +
          ∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₂), Y i ω / 2 ^ ℓ) - μ|}
      ≤ 2 * Real.exp (-2 * ε ^ 2 * ((η₁ : ℝ) + η₂ / 2 ^ ℓ)) := by sorry

end FakeUserRanking.FORC

