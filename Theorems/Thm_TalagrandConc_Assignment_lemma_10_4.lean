import Mathlib

namespace TalagrandConc.Assignment

open MeasureTheory ProbabilityTheory

/-- Talagrand (1995), p. 168, Lemma 10.4. For every `δ < 1` there is `K(δ) > 0`, depending
on `δ` only, such that for independent events `A_1, …, A_N` with `P(A_i) = p`, the
probability that fewer than `δ p N` of the events occur is at most `exp(−N p / K(δ))`. -/
theorem lemma_10_4 :
    ∀ δ : ℝ, δ < 1 → ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : ℕ) (A : Fin N → Set Ω) (p : ℝ),
        (∀ i, MeasurableSet (A i)) → iIndepSet A P → (∀ i, P.real (A i) = p) →
        P {ω | (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) < δ * p * N} ≤
          ENNReal.ofReal (Real.exp (-((N : ℝ) * p) / K)) := by sorry

end TalagrandConc.Assignment

