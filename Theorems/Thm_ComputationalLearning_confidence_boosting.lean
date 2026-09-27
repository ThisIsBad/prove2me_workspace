import Definitions.Def_ComputationalLearning_Boosting

open MeasureTheory ProbabilityTheory


namespace ComputationalLearning

/-- **Boosting the confidence** (§4.2, pp. 76–77). (i) If a learner `L` on samples of size `m` finds
a hypothesis of error at most `ε` with probability at least `δ₀` (for the target `c` and
distribution `D`), then on `k` independent samples all `k` hypotheses have error greater than
`ε` with probability at most `(1 − δ₀)^k` (at most `δ/2` for `k ≥ (1/δ₀) ln(2/δ)`). (ii) Given
hypotheses `h₁, …, h_k` at least one of which has error at most `ε`, choosing on a fresh sample
of `m` examples a hypothesis with the fewest mistakes yields, with probability at least
`1 − 2k e^{−mγ²/2}` (the Chernoff bound with accuracy `γ/2` for each of the `k` hypotheses and
the union bound), a hypothesis of error at most `ε + γ`; the book's `(c₀/γ²) log(2k/δ)` examples
are `m ≥ (2/γ²) ln(4k/δ)` with this constant. -/
theorem confidence_boosting {X : Type*} [MeasurableSpace X] (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] {ε : ℝ} :
    (∀ (m : ℕ) (L : (Fin m → X × Bool) → X → Bool) {δ₀ : ℝ}, 0 ≤ δ₀ → δ₀ ≤ 1 →
      sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal (1 - δ₀) →
      ∀ k : ℕ, blockSampleLaw D c k m {B | ∀ i, ε < errorOf D c (L (B i))} ≤
        ENNReal.ofReal ((1 - δ₀) ^ k)) ∧
    (∀ (k : ℕ) (h : Fin k → X → Bool), (∀ i, Measurable (h i)) → (∃ i, errorOf D c (h i) ≤ ε) →
      ∀ {γ : ℝ}, 0 < γ → ∀ (m : ℕ) (sel : (Fin m → X × Bool) → Fin k),
        (∀ S j, mistakes (h (sel S)) S ≤ mistakes (h j) S) →
        sampleLaw D c m {S | ε + γ < errorOf D c (h (sel S))} ≤
          ENNReal.ofReal (2 * k * Real.exp (-(m * γ ^ 2 / 2)))) := by sorry

end ComputationalLearning

